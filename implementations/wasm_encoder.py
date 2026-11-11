"""Encode the canonical JSON of the Wasm SpecTec `module` AST into the binary format.

The input is the Lean `deriving ToJson` form used by property requests:
a nullary constructor is `"Name"`, a constructor with one argument is
`{"Name": arg}`, one with several arguments is `{"Name": [args...]}`,
structures are objects keyed by field name, `Option` is `null` or the value,
and pairs are two-element arrays.

The encoder is part of the trusted boundary between the specification and an
engine. It raises `Unencodable` instead of guessing when an AST has no
binary-format counterpart. Examples are values outside u32/u64 or the numeric
type's range, non-canonical float magnitudes, `RecX` outside a recursion
group, runtime-only types (`DefHT`, `BotHT`, `BotT`), and vector shape/operator
pairs without an opcode. Validity is not checked here; invalid but encodable
modules are encoded faithfully so the engine can reject them.

Where the binary format allows several encodings, the encoder emits the bytes
that wat2wasm emits for the corresponding text, with three fixed choices: a
singleton recursion group is written bare, a table always carries its
initializer expression, and a data count section accompanies any data segment.
"""

import struct


class Unencodable(ValueError):
    """The module AST has no binary-format encoding."""


# ---------------------------------------------------------------------------
# Canonical JSON helpers

def _ctor(value, where):
    if isinstance(value, str):
        return value, None
    if isinstance(value, dict) and len(value) == 1:
        (name, payload), = value.items()
        return name, payload
    raise Unencodable(f'{where}: expected a constructor, got {value!r}')


def _args(payload, count, where):
    if count == 1:
        return [payload]
    if not isinstance(payload, list) or len(payload) != count:
        raise Unencodable(f'{where}: expected {count} constructor arguments, got {payload!r}')
    return payload


def _list(value, where):
    if not isinstance(value, list):
        raise Unencodable(f'{where}: expected a list, got {value!r}')
    return value


def _nat(value, where):
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise Unencodable(f'{where}: expected a natural number, got {value!r}')
    return value


def _field(record, name, where):
    if not isinstance(record, dict) or name not in record:
        raise Unencodable(f'{where}: missing field {name}')
    return record[name]


# ---------------------------------------------------------------------------
# Integers

def _uleb(n):
    out = bytearray()
    while True:
        byte = n & 0x7F
        n >>= 7
        if n:
            out.append(byte | 0x80)
        else:
            out.append(byte)
            return bytes(out)


def _sleb(n):
    out = bytearray()
    while True:
        byte = n & 0x7F
        n >>= 7
        if (n == 0 and not byte & 0x40) or (n == -1 and byte & 0x40):
            out.append(byte)
            return bytes(out)
        out.append(byte | 0x80)


def u32(value, where='u32'):
    value = _nat(value, where)
    if value >= 1 << 32:
        raise Unencodable(f'{where}: {value} does not fit in u32')
    return _uleb(value)


def u64(value, where='u64'):
    value = _nat(value, where)
    if value >= 1 << 64:
        raise Unencodable(f'{where}: {value} does not fit in u64')
    return _uleb(value)


def _signed(value, bits, where):
    value = _nat(value, where)
    if value >= 1 << bits:
        raise Unencodable(f'{where}: {value} does not fit in i{bits}')
    return value - (1 << bits) if value >= 1 << (bits - 1) else value


def _byte(value, where):
    value = _nat(value, where)
    if value > 0xFF:
        raise Unencodable(f'{where}: {value} does not fit in a byte')
    return bytes([value])


def _vec(items):
    items = list(items)
    return u32(len(items), 'vector length') + b''.join(items)


def _name(chars, where):
    out = []
    for c in _list(chars, where):
        c = _nat(c, where)
        if c > 0x10FFFF or 0xD800 <= c <= 0xDFFF:
            raise Unencodable(f'{where}: {c:#x} is not a Unicode scalar value')
        out.append(chr(c))
    data = ''.join(out).encode('utf-8')
    return u32(len(data), where) + data


# ---------------------------------------------------------------------------
# Floats: fmag mirrors the specification's to32/to64 bit layout.

_FLOAT = {32: (23, 8, 127), 64: (52, 11, 1023)}


def float_bits(value, width, where):
    mant_bits, exp_bits, bias = _FLOAT[width]
    sign_name, mag = _ctor(value, where)
    if sign_name not in ('POS', 'NEG'):
        raise Unencodable(f'{where}: unknown float sign {sign_name}')
    kind, payload = _ctor(mag, where)
    max_exp = (1 << exp_bits) - 1
    if kind == 'NORM':
        m, e = _args(payload, 2, where)
        m = _nat(m, where)
        if isinstance(e, bool) or not isinstance(e, int):
            raise Unencodable(f'{where}: exponent must be an integer')
        field = e + bias
        if m >= 1 << mant_bits or not 1 <= field < max_exp:
            raise Unencodable(f'{where}: non-canonical normal magnitude {payload!r}')
        bits = (field << mant_bits) | m
    elif kind == 'SUBNORM':
        m = _nat(payload, where)
        if m >= 1 << mant_bits:
            raise Unencodable(f'{where}: non-canonical subnormal magnitude {m}')
        bits = m
    elif kind == 'INF' and payload is None:
        bits = max_exp << mant_bits
    elif kind == 'NAN':
        m = _nat(payload, where)
        if not 1 <= m < 1 << mant_bits:
            raise Unencodable(f'{where}: NaN payload {m} is not a NaN')
        bits = (max_exp << mant_bits) | m
    else:
        raise Unencodable(f'{where}: unknown float magnitude {kind}')
    if sign_name == 'NEG':
        bits |= 1 << (width - 1)
    return bits


# ---------------------------------------------------------------------------
# Opcode tables

NUMTYPE = {'I32T': 0x7F, 'I64T': 0x7E, 'F32T': 0x7D, 'F64T': 0x7C}
ABSHEAP = {'FuncHT': 0x70, 'ExternHT': 0x6F, 'AnyHT': 0x6E, 'EqHT': 0x6D,
           'I31HT': 0x6C, 'StructHT': 0x6B, 'ArrayHT': 0x6A, 'ExnHT': 0x69,
           'NoExnHT': 0x74, 'NoFuncHT': 0x73, 'NoExternHT': 0x72, 'NoneHT': 0x71}
MUT = {'Cons': 0x00, 'Var': 0x01}

LOAD = {('I32T', None): 0x28, ('I64T', None): 0x29, ('F32T', None): 0x2A, ('F64T', None): 0x2B,
        ('I32T', 'I8', 'SX'): 0x2C, ('I32T', 'I8', 'ZX'): 0x2D,
        ('I32T', 'I16', 'SX'): 0x2E, ('I32T', 'I16', 'ZX'): 0x2F,
        ('I64T', 'I8', 'SX'): 0x30, ('I64T', 'I8', 'ZX'): 0x31,
        ('I64T', 'I16', 'SX'): 0x32, ('I64T', 'I16', 'ZX'): 0x33,
        ('I64T', 'I32', 'SX'): 0x34, ('I64T', 'I32', 'ZX'): 0x35}
STORE = {('I32T', None): 0x36, ('I64T', None): 0x37, ('F32T', None): 0x38, ('F64T', None): 0x39,
         ('I32T', 'I8'): 0x3A, ('I32T', 'I16'): 0x3B,
         ('I64T', 'I8'): 0x3C, ('I64T', 'I16'): 0x3D, ('I64T', 'I32'): 0x3E}

TESTOP = {('I32', 'Eqz'): 0x45, ('I64', 'Eqz'): 0x50}
_IREL = ['Eq', 'Ne', 'LtS', 'LtU', 'GtS', 'GtU', 'LeS', 'LeU', 'GeS', 'GeU']
_FREL = ['Eq', 'Ne', 'Lt', 'Gt', 'Le', 'Ge']
RELOP = {**{('I32', op): 0x46 + i for i, op in enumerate(_IREL)},
         **{('I64', op): 0x51 + i for i, op in enumerate(_IREL)},
         **{('F32', op): 0x5B + i for i, op in enumerate(_FREL)},
         **{('F64', op): 0x61 + i for i, op in enumerate(_FREL)}}
_IUN = ['Clz', 'Ctz', 'Popcnt']
_FUN = ['Abs', 'Neg', 'Ceil', 'Floor', 'Trunc', 'Nearest', 'Sqrt']
UNOP = {**{('I32', op): 0x67 + i for i, op in enumerate(_IUN)},
        **{('I64', op): 0x79 + i for i, op in enumerate(_IUN)},
        **{('F32', op): 0x8B + i for i, op in enumerate(_FUN)},
        **{('F64', op): 0x99 + i for i, op in enumerate(_FUN)}}
EXTENDS = {('I32', 'I8'): 0xC0, ('I32', 'I16'): 0xC1,
           ('I64', 'I8'): 0xC2, ('I64', 'I16'): 0xC3, ('I64', 'I32'): 0xC4}
_IBIN = ['IAdd', 'ISub', 'IMul', 'IDivS', 'IDivU', 'IRemS', 'IRemU', 'IAnd', 'IOr', 'IXor',
         'IShl', 'IShrS', 'IShrU', 'IRotl', 'IRotr']
_FBIN = ['FAdd', 'FSub', 'FMul', 'FDiv', 'FMin', 'FMax', 'FCopysign']
BINOP = {**{('I32', op): 0x6A + i for i, op in enumerate(_IBIN)},
         **{('I64', op): 0x7C + i for i, op in enumerate(_IBIN)},
         **{('F32', op): 0x92 + i for i, op in enumerate(_FBIN)},
         **{('F64', op): 0xA0 + i for i, op in enumerate(_FBIN)}}
# Keys are (result type, operator), matching $eval_cvtop. Values are bytes so
# the saturating conversions can carry their 0xFC prefix.
CVTOP = {('I32', 'WrapI64'): b'\xa7',
         ('I32', 'TruncSF32'): b'\xa8', ('I32', 'TruncUF32'): b'\xa9',
         ('I32', 'TruncSF64'): b'\xaa', ('I32', 'TruncUF64'): b'\xab',
         ('I64', 'ExtendSI32'): b'\xac', ('I64', 'ExtendUI32'): b'\xad',
         ('I64', 'TruncSF32'): b'\xae', ('I64', 'TruncUF32'): b'\xaf',
         ('I64', 'TruncSF64'): b'\xb0', ('I64', 'TruncUF64'): b'\xb1',
         ('F32', 'ConvertSI32'): b'\xb2', ('F32', 'ConvertUI32'): b'\xb3',
         ('F32', 'ConvertSI64'): b'\xb4', ('F32', 'ConvertUI64'): b'\xb5',
         ('F32', 'DemoteF64'): b'\xb6',
         ('F64', 'ConvertSI32'): b'\xb7', ('F64', 'ConvertUI32'): b'\xb8',
         ('F64', 'ConvertSI64'): b'\xb9', ('F64', 'ConvertUI64'): b'\xba',
         ('F64', 'PromoteF32'): b'\xbb',
         ('I32', 'ReinterpretFloat'): b'\xbc', ('I64', 'ReinterpretFloat'): b'\xbd',
         ('F32', 'ReinterpretInt'): b'\xbe', ('F64', 'ReinterpretInt'): b'\xbf',
         ('I32', 'TruncSatSF32'): b'\xfc\x00', ('I32', 'TruncSatUF32'): b'\xfc\x01',
         ('I32', 'TruncSatSF64'): b'\xfc\x02', ('I32', 'TruncSatUF64'): b'\xfc\x03',
         ('I64', 'TruncSatSF32'): b'\xfc\x04', ('I64', 'TruncSatUF32'): b'\xfc\x05',
         ('I64', 'TruncSatSF64'): b'\xfc\x06', ('I64', 'TruncSatUF64'): b'\xfc\x07'}

# SIMD (0xFD prefix). Shapes name the result lanes, as in the builtins.
VTEST = {('I8x16', 'AllTrue'): 99, ('I16x8', 'AllTrue'): 131,
         ('I32x4', 'AllTrue'): 163, ('I64x2', 'AllTrue'): 195}
VUNOP = {('I8x16', 'Abs'): 96, ('I8x16', 'Neg'): 97, ('I8x16', 'Popcnt'): 98,
         ('I16x8', 'Abs'): 128, ('I16x8', 'Neg'): 129,
         ('I32x4', 'Abs'): 160, ('I32x4', 'Neg'): 161,
         ('I64x2', 'Abs'): 192, ('I64x2', 'Neg'): 193,
         ('F32x4', 'Ceil'): 103, ('F32x4', 'Floor'): 104, ('F32x4', 'Trunc'): 105,
         ('F32x4', 'Nearest'): 106, ('F32x4', 'Abs'): 224, ('F32x4', 'Neg'): 225,
         ('F32x4', 'Sqrt'): 227,
         ('F64x2', 'Ceil'): 116, ('F64x2', 'Floor'): 117, ('F64x2', 'Trunc'): 122,
         ('F64x2', 'Nearest'): 148, ('F64x2', 'Abs'): 236, ('F64x2', 'Neg'): 237,
         ('F64x2', 'Sqrt'): 239}
VBINOP = {('I8x16', 'Swizzle'): 14, ('I8x16', 'NarrowS'): 101, ('I8x16', 'NarrowU'): 102,
          ('I8x16', 'Add'): 110, ('I8x16', 'AddSatS'): 111, ('I8x16', 'AddSatU'): 112,
          ('I8x16', 'Sub'): 113, ('I8x16', 'SubSatS'): 114, ('I8x16', 'SubSatU'): 115,
          ('I8x16', 'MinS'): 118, ('I8x16', 'MinU'): 119, ('I8x16', 'MaxS'): 120,
          ('I8x16', 'MaxU'): 121, ('I8x16', 'AvgrU'): 123, ('I8x16', 'RelaxedSwizzle'): 256,
          ('I16x8', 'Q15MulRSatS'): 130, ('I16x8', 'NarrowS'): 133, ('I16x8', 'NarrowU'): 134,
          ('I16x8', 'Add'): 142, ('I16x8', 'AddSatS'): 143, ('I16x8', 'AddSatU'): 144,
          ('I16x8', 'Sub'): 145, ('I16x8', 'SubSatS'): 146, ('I16x8', 'SubSatU'): 147,
          ('I16x8', 'Mul'): 149, ('I16x8', 'MinS'): 150, ('I16x8', 'MinU'): 151,
          ('I16x8', 'MaxS'): 152, ('I16x8', 'MaxU'): 153, ('I16x8', 'AvgrU'): 155,
          ('I16x8', 'ExtMulLowS'): 156, ('I16x8', 'ExtMulHighS'): 157,
          ('I16x8', 'ExtMulLowU'): 158, ('I16x8', 'ExtMulHighU'): 159,
          ('I16x8', 'RelaxedQ15MulRS'): 273, ('I16x8', 'RelaxedDot'): 274,
          ('I32x4', 'Add'): 174, ('I32x4', 'Sub'): 177, ('I32x4', 'Mul'): 181,
          ('I32x4', 'MinS'): 182, ('I32x4', 'MinU'): 183, ('I32x4', 'MaxS'): 184,
          ('I32x4', 'MaxU'): 185, ('I32x4', 'DotS'): 186,
          ('I32x4', 'ExtMulLowS'): 188, ('I32x4', 'ExtMulHighS'): 189,
          ('I32x4', 'ExtMulLowU'): 190, ('I32x4', 'ExtMulHighU'): 191,
          ('I64x2', 'Add'): 206, ('I64x2', 'Sub'): 209, ('I64x2', 'Mul'): 213,
          ('I64x2', 'ExtMulLowS'): 220, ('I64x2', 'ExtMulHighS'): 221,
          ('I64x2', 'ExtMulLowU'): 222, ('I64x2', 'ExtMulHighU'): 223,
          ('F32x4', 'Add'): 228, ('F32x4', 'Sub'): 229, ('F32x4', 'Mul'): 230,
          ('F32x4', 'Div'): 231, ('F32x4', 'Min'): 232, ('F32x4', 'Max'): 233,
          ('F32x4', 'Pmin'): 234, ('F32x4', 'Pmax'): 235,
          ('F32x4', 'RelaxedMin'): 269, ('F32x4', 'RelaxedMax'): 270,
          ('F64x2', 'Add'): 240, ('F64x2', 'Sub'): 241, ('F64x2', 'Mul'): 242,
          ('F64x2', 'Div'): 243, ('F64x2', 'Min'): 244, ('F64x2', 'Max'): 245,
          ('F64x2', 'Pmin'): 246, ('F64x2', 'Pmax'): 247,
          ('F64x2', 'RelaxedMin'): 271, ('F64x2', 'RelaxedMax'): 272}
VTERNOP = {('I8x16', 'RelaxedLaneselect'): 265, ('I16x8', 'RelaxedLaneselect'): 266,
           ('I32x4', 'RelaxedLaneselect'): 267, ('I64x2', 'RelaxedLaneselect'): 268,
           ('I32x4', 'RelaxedDotAdd'): 275,
           ('F32x4', 'RelaxedMadd'): 261, ('F32x4', 'RelaxedNmadd'): 262,
           ('F64x2', 'RelaxedMadd'): 263, ('F64x2', 'RelaxedNmadd'): 264}
VRELOP = {**{('I8x16', op): 35 + i for i, op in enumerate(_IREL)},
          **{('I16x8', op): 45 + i for i, op in enumerate(_IREL)},
          **{('I32x4', op): 55 + i for i, op in enumerate(_IREL)},
          ('I64x2', 'Eq'): 214, ('I64x2', 'Ne'): 215, ('I64x2', 'LtS'): 216,
          ('I64x2', 'GtS'): 217, ('I64x2', 'LeS'): 218, ('I64x2', 'GeS'): 219,
          **{('F32x4', op): 65 + i for i, op in enumerate(_FREL)},
          **{('F64x2', op): 71 + i for i, op in enumerate(_FREL)}}
VCVTOP = {('I16x8', 'ExtAddPairwiseS'): 124, ('I16x8', 'ExtAddPairwiseU'): 125,
          ('I16x8', 'ExtendLowS'): 135, ('I16x8', 'ExtendHighS'): 136,
          ('I16x8', 'ExtendLowU'): 137, ('I16x8', 'ExtendHighU'): 138,
          ('I32x4', 'ExtAddPairwiseS'): 126, ('I32x4', 'ExtAddPairwiseU'): 127,
          ('I32x4', 'ExtendLowS'): 167, ('I32x4', 'ExtendHighS'): 168,
          ('I32x4', 'ExtendLowU'): 169, ('I32x4', 'ExtendHighU'): 170,
          ('I32x4', 'TruncSatSF32x4'): 248, ('I32x4', 'TruncSatUF32x4'): 249,
          ('I32x4', 'TruncSatSZeroF64x2'): 252, ('I32x4', 'TruncSatUZeroF64x2'): 253,
          ('I32x4', 'RelaxedTruncSF32x4'): 257, ('I32x4', 'RelaxedTruncUF32x4'): 258,
          ('I32x4', 'RelaxedTruncSZeroF64x2'): 259, ('I32x4', 'RelaxedTruncUZeroF64x2'): 260,
          ('I64x2', 'ExtendLowS'): 199, ('I64x2', 'ExtendHighS'): 200,
          ('I64x2', 'ExtendLowU'): 201, ('I64x2', 'ExtendHighU'): 202,
          ('F32x4', 'DemoteZeroF64x2'): 94, ('F32x4', 'ConvertSI32x4'): 250,
          ('F32x4', 'ConvertUI32x4'): 251,
          ('F64x2', 'PromoteLowF32x4'): 95, ('F64x2', 'ConvertSI32x4'): 254,
          ('F64x2', 'ConvertUI32x4'): 255}
VSHIFT = {(shape, op): base + i
          for shape, base in (('I8x16', 107), ('I16x8', 139), ('I32x4', 171), ('I64x2', 203))
          for i, op in enumerate(['Shl', 'ShrS', 'ShrU'])}
VBITMASK = {('I8x16', 'Bitmask'): 100, ('I16x8', 'Bitmask'): 132,
            ('I32x4', 'Bitmask'): 164, ('I64x2', 'Bitmask'): 196}
VVTEST = {'AnyTrue': 83}
VVUNOP = {'Not': 77}
VVBINOP = {'And': 78, 'AndNot': 79, 'Or': 80, 'Xor': 81}
VVTERNOP = {'Bitselect': 82}
VSPLAT = {'I8x16': 15, 'I16x8': 16, 'I32x4': 17, 'I64x2': 18, 'F32x4': 19, 'F64x2': 20}
VEXTRACT = {('I8x16', 'SX'): 21, ('I8x16', 'ZX'): 22, ('I16x8', 'SX'): 24, ('I16x8', 'ZX'): 25,
            ('I32x4', 'VOID'): 27, ('I64x2', 'VOID'): 29, ('F32x4', 'VOID'): 31,
            ('F64x2', 'VOID'): 33}
VREPLACE = {'I8x16': 23, 'I16x8': 26, 'I32x4': 28, 'I64x2': 30, 'F32x4': 32, 'F64x2': 34}
# Vector loads. This specification has no execution rule for ExtLane; the
# loaded width is taken to be the packtype (I64 for 8x8/16x4/32x2), matching
# the alignment bound 2^align <= $pack_size(packtype) and the official ops.
VLOAD_LANE = {('I64', 'Pack8x8', 'SX'): 1, ('I64', 'Pack8x8', 'ZX'): 2,
              ('I64', 'Pack16x4', 'SX'): 3, ('I64', 'Pack16x4', 'ZX'): 4,
              ('I64', 'Pack32x2', 'SX'): 5, ('I64', 'Pack32x2', 'ZX'): 6}
VLOAD_SPLAT = {'I8': 7, 'I16': 8, 'I32': 9, 'I64': 10}
VLOAD_ZERO = {'I32': 92, 'I64': 93}
VLANE_LOAD = {'I8': 84, 'I16': 85, 'I32': 86, 'I64': 87}
VLANE_STORE = {'I8': 88, 'I16': 89, 'I32': 90, 'I64': 91}


def _prefixed(prefix, code):
    return bytes([prefix]) + _uleb(code)


def _lookup(table, key, where):
    if key not in table:
        raise Unencodable(f'{where}: no binary opcode for {key!r}')
    return table[key]


# ---------------------------------------------------------------------------
# Encoder

class _Encoder:
    def __init__(self):
        self.rec_base = None  # absolute index of the current recursion group
        self.code_sizes = []  # encoded size of each function body, for limit checks

    # Types ------------------------------------------------------------------

    def typevar(self, value, where):
        name, payload = _ctor(value, where)
        if name == 'StatX':
            return _nat(payload, where)
        if name == 'RecX':
            if self.rec_base is None:
                raise Unencodable(f'{where}: RecX outside a recursion group')
            return self.rec_base + _nat(payload, where)
        raise Unencodable(f'{where}: unknown type variable {name}')

    def heaptype(self, value, where='heaptype'):
        name, payload = _ctor(value, where)
        if name in ABSHEAP and payload is None:
            return bytes([ABSHEAP[name]])
        if name == 'VarHT':
            index = self.typevar(payload, where)
            if index >= 1 << 32:
                raise Unencodable(f'{where}: type index {index} does not fit in u32')
            return _sleb(index)
        raise Unencodable(f'{where}: {name} is not a syntactic heap type')

    def reftype(self, value, where='reftype'):
        name, payload = _ctor(value, where)
        if name != '% %':
            raise Unencodable(f'{where}: unknown reference type {name}')
        null, heap = _args(payload, 2, where)
        prefix = {'Null': 0x63, 'NoNull': 0x64}.get(null)
        if prefix is None:
            raise Unencodable(f'{where}: unknown nullability {null!r}')
        encoded = self.heaptype(heap, where)
        if null == 'Null' and _ctor(heap, where)[0] in ABSHEAP:
            return encoded  # shorthand: a nullable abstract type is its heap type byte
        return bytes([prefix]) + encoded

    def valtype(self, value, where='valtype'):
        name, payload = _ctor(value, where)
        if name == 'NumT':
            return bytes([_lookup(NUMTYPE, payload, where)])
        if name == 'VecT' and payload == 'V128T':
            return b'\x7b'
        if name == 'RefT':
            return self.reftype(payload, where)
        raise Unencodable(f'{where}: {name} is not a syntactic value type')

    def storagetype(self, value, where):
        name, payload = _ctor(value, where)
        if name == 'ValStorageT':
            return self.valtype(payload, where)
        if name == 'PackStorageT':
            return bytes([_lookup({'I8': 0x78, 'I16': 0x77}, payload, where)])
        raise Unencodable(f'{where}: unknown storage type {name}')

    def fieldtype(self, value, where):
        name, payload = _ctor(value, where)
        if name != 'FieldT':
            raise Unencodable(f'{where}: unknown field type {name}')
        mut, storage = _args(payload, 2, where)
        return self.storagetype(storage, where) + bytes([_lookup(MUT, mut, where)])

    def strtype(self, value, where):
        name, payload = _ctor(value, where)
        if name == 'DefFuncT':
            fname, fpayload = _ctor(payload, where)
            if fname != 'FuncT':
                raise Unencodable(f'{where}: unknown function type {fname}')
            params, results = _args(fpayload, 2, where)
            return (b'\x60' + _vec(self.valtype(t, where) for t in _list(params, where))
                    + _vec(self.valtype(t, where) for t in _list(results, where)))
        if name == 'DefStructT':
            sname, fields = _ctor(payload, where)
            if sname != 'StructT':
                raise Unencodable(f'{where}: unknown struct type {sname}')
            return b'\x5f' + _vec(self.fieldtype(f, where) for f in _list(fields, where))
        if name == 'DefArrayT':
            aname, field = _ctor(payload, where)
            if aname != 'ArrayT':
                raise Unencodable(f'{where}: unknown array type {aname}')
            return b'\x5e' + self.fieldtype(field, where)
        raise Unencodable(f'{where}: unknown composite type {name}')

    def subtype(self, value, where):
        name, payload = _ctor(value, where)
        if name != 'SubT':
            raise Unencodable(f'{where}: unknown subtype {name}')
        final, supers, strtype = _args(payload, 3, where)
        if final not in ('Final', 'NoFinal'):
            raise Unencodable(f'{where}: unknown finality {final!r}')
        body = self.strtype(strtype, where)
        supers = _list(supers, where)
        if final == 'Final' and not supers:
            return body
        indices = []
        for heap in supers:
            hname, hpayload = _ctor(heap, where)
            if hname != 'VarHT':
                raise Unencodable(f'{where}: supertype {hname} is not a type index')
            indices.append(u32(self.typevar(hpayload, where), where))
        return bytes([0x4F if final == 'Final' else 0x50]) + _vec(indices) + body

    def rectype(self, value, base, where):
        name, subtypes = _ctor(value, where)
        if name != 'RecT':
            raise Unencodable(f'{where}: unknown recursive type {name}')
        subtypes = _list(subtypes, where)
        self.rec_base = base
        try:
            encoded = [self.subtype(s, f'{where}.{i}') for i, s in enumerate(subtypes)]
        finally:
            self.rec_base = None
        if len(encoded) == 1:
            return encoded[0], 1
        return b'\x4e' + _vec(encoded), len(encoded)

    def limits(self, addrtype, lim, where):
        if addrtype not in ('I32AT', 'I64AT'):
            raise Unencodable(f'{where}: unknown address type {addrtype!r}')
        bound = u64 if addrtype == 'I64AT' else u32
        low = _field(lim, 'MIN', where)
        high = _field(lim, 'MAX', where)
        flags = (0x04 if addrtype == 'I64AT' else 0) | (0x01 if high is not None else 0)
        out = bytes([flags]) + bound(low, where + '.MIN')
        if high is not None:
            out += bound(high, where + '.MAX')
        return out

    def tabletype(self, value, where):
        name, payload = _ctor(value, where)
        if name != 'TableT':
            raise Unencodable(f'{where}: unknown table type {name}')
        addrtype, lim, ref = _args(payload, 3, where)
        return self.reftype(ref, where) + self.limits(addrtype, lim, where)

    def memtype(self, value, where):
        name, payload = _ctor(value, where)
        if name != 'MemoryT':
            raise Unencodable(f'{where}: unknown memory type {name}')
        addrtype, lim = _args(payload, 2, where)
        return self.limits(addrtype, lim, where)

    def globaltype(self, value, where):
        name, payload = _ctor(value, where)
        if name != 'GlobalT':
            raise Unencodable(f'{where}: unknown global type {name}')
        mut, valtype = _args(payload, 2, where)
        return self.valtype(valtype, where) + bytes([_lookup(MUT, mut, where)])

    def blocktype(self, value, where):
        name, payload = _ctor(value, where)
        if name == 'VarBlockType':
            index = _nat(payload, where)
            if index >= 1 << 32:
                raise Unencodable(f'{where}: block type index {index} does not fit')
            return _sleb(index)
        if name == 'ValBlockType':
            return b'\x40' if payload is None else self.valtype(payload, where)
        raise Unencodable(f'{where}: unknown block type {name}')

    # Instructions -----------------------------------------------------------

    def memarg(self, memidx, memop, where):
        align = _nat(_field(memop, 'ALIGN', where), where + '.ALIGN')
        if align >= 64:
            raise Unencodable(f'{where}: alignment exponent {align} does not fit the memarg flags')
        memidx = _nat(memidx, where)
        flags = align | (0x40 if memidx else 0)
        out = u32(flags, where)
        if memidx:
            out += u32(memidx, where)
        return out + u64(_field(memop, 'OFFSET', where), where + '.OFFSET')

    def expr(self, instrs, where):
        return b''.join(self.instr(i, f'{where}.{n}') for n, i in enumerate(_list(instrs, where))) + b'\x0b'

    def instrs(self, instrs, where):
        return b''.join(self.instr(i, f'{where}.{n}') for n, i in enumerate(_list(instrs, where)))

    def _vecop(self, payload, where):
        """Unwrap `V128 (shape op)` into (shape, op payload)."""
        vname, lane = _ctor(payload, where)
        if vname != 'V128':
            raise Unencodable(f'{where}: unknown vector type {vname}')
        return _ctor(lane, where)

    def instr(self, value, where):
        name, p = _ctor(value, where)
        simple = {'UNREACHABLE': b'\x00', 'NOP': b'\x01', 'DROP': b'\x1a', 'RETURN': b'\x0f',
                  'THROW_REF': b'\x0a', 'REF.IS_NULL': b'\xd1', 'REF.AS_NON_NULL': b'\xd4',
                  'REF.EQ': b'\xd3', 'REF.I31': b'\xfb\x1c', 'ARRAY.LEN': b'\xfb\x0f'}
        if name in simple and p is None:
            return simple[name]
        index1 = {'BR': b'\x0c', 'BR_IF': b'\x0d', 'BR_ON_NULL': b'\xd5', 'BR_ON_NON_NULL': b'\xd6',
                  'CALL': b'\x10', 'CALL_REF': b'\x14', 'RETURN_CALL': b'\x12',
                  'RETURN_CALL_REF': b'\x15', 'THROW': b'\x08',
                  'LOCAL.GET': b'\x20', 'LOCAL.SET': b'\x21', 'LOCAL.TEE': b'\x22',
                  'GLOBAL.GET': b'\x23', 'GLOBAL.SET': b'\x24',
                  'TABLE.GET': b'\x25', 'TABLE.SET': b'\x26',
                  'TABLE.GROW': b'\xfc\x0f', 'TABLE.SIZE': b'\xfc\x10', 'TABLE.FILL': b'\xfc\x11',
                  'ELEM.DROP': b'\xfc\x0d', 'MEMORY.SIZE': b'\x3f', 'MEMORY.GROW': b'\x40',
                  'MEMORY.FILL': b'\xfc\x0b', 'DATA.DROP': b'\xfc\x09', 'REF.FUNC': b'\xd2',
                  'ARRAY.SET': b'\xfb\x0e', 'ARRAY.FILL': b'\xfb\x10'}
        if name in index1:
            return index1[name] + u32(p, where)
        # Two indices, written in the binary order.
        index2 = {'TABLE.COPY': (b'\xfc\x0e', False), 'TABLE.INIT': (b'\xfc\x0c', True),
                  'MEMORY.COPY': (b'\xfc\x0a', False), 'MEMORY.INIT': (b'\xfc\x08', True),
                  'CALL_INDIRECT': (b'\x11', True), 'RETURN_CALL_INDIRECT': (b'\x13', True),
                  'STRUCT.SET': (b'\xfb\x05', False), 'ARRAY.NEW_FIXED': (b'\xfb\x08', False),
                  'ARRAY.NEW_DATA': (b'\xfb\x09', False), 'ARRAY.NEW_ELEM': (b'\xfb\x0a', False),
                  'ARRAY.COPY': (b'\xfb\x11', False), 'ARRAY.INIT_DATA': (b'\xfb\x12', False),
                  'ARRAY.INIT_ELEM': (b'\xfb\x13', False)}
        if name in index2:
            code, swap = index2[name]
            a, b = _args(p, 2, where)
            if swap:  # AST (table, type)/(table, elem)/(memory, data); binary is reversed
                a, b = b, a
            return code + u32(a, where) + u32(b, where)
        if name == 'SELECT':
            if p is None:
                return b'\x1b'
            return b'\x1c' + _vec(self.valtype(t, where) for t in _list(p, where))
        if name in ('BLOCK', 'LOOP'):
            bt, body = _args(p, 2, where)
            return ((b'\x02' if name == 'BLOCK' else b'\x03') + self.blocktype(bt, where)
                    + self.expr(body, where))
        if name == 'IF % % ELSE %':
            bt, then, other = _args(p, 3, where)
            out = b'\x04' + self.blocktype(bt, where) + self.instrs(then, where)
            if _list(other, where):
                out += b'\x05' + self.instrs(other, where)
            return out + b'\x0b'
        if name == 'TRY_TABLE':
            bt, catches, body = _args(p, 3, where)
            return (b'\x1f' + self.blocktype(bt, where)
                    + _vec(self.catch(c, where) for c in _list(catches, where))
                    + self.expr(body, where))
        if name == 'BR_TABLE':
            labels, default = _args(p, 2, where)
            return b'\x0e' + _vec(u32(l, where) for l in _list(labels, where)) + u32(default, where)
        if name in ('BR_ON_CAST', 'BR_ON_CAST_FAIL'):
            label, rt1, rt2 = _args(p, 3, where)
            null1, heap1 = self._ref_parts(rt1, where)
            null2, heap2 = self._ref_parts(rt2, where)
            flags = (1 if null1 else 0) | (2 if null2 else 0)
            code = b'\xfb\x18' if name == 'BR_ON_CAST' else b'\xfb\x19'
            return (code + bytes([flags]) + u32(label, where)
                    + self.heaptype(heap1, where) + self.heaptype(heap2, where))
        if name in ('REF.TEST', 'REF.CAST'):
            null, heap = self._ref_parts(p, where)
            code = {('REF.TEST', False): 20, ('REF.TEST', True): 21,
                    ('REF.CAST', False): 22, ('REF.CAST', True): 23}[(name, null)]
            return _prefixed(0xFB, code) + self.heaptype(heap, where)
        if name == 'REF.NULL':
            return b'\xd0' + self.heaptype(p, where)
        if name == 'I31.GET':
            return _prefixed(0xFB, _lookup({'SX': 29, 'ZX': 30}, p, where))
        if name in ('STRUCT.NEW', 'ARRAY.NEW'):
            x, init = _args(p, 2, where)
            codes = {'STRUCT.NEW': {'Explicit': 0, 'Implicit': 1},
                     'ARRAY.NEW': {'Explicit': 6, 'Implicit': 7}}[name]
            return _prefixed(0xFB, _lookup(codes, init, where)) + u32(x, where)
        if name == 'STRUCT.GET':
            x, i, ext = _args(p, 3, where)
            code = _lookup({None: 2, 'SX': 3, 'ZX': 4}, ext, where)
            return _prefixed(0xFB, code) + u32(x, where) + u32(i, where)
        if name == 'ARRAY.GET':
            x, ext = _args(p, 2, where)
            code = _lookup({None: 11, 'SX': 12, 'ZX': 13}, ext, where)
            return _prefixed(0xFB, code) + u32(x, where)
        if name == 'EXTERN.CONVERT':
            return _prefixed(0xFB, _lookup({'Internalize': 26, 'Externalize': 27}, p, where))
        if name in ('LOAD', 'STORE'):
            x, memop = _args(p, 2, where)
            numtype = _field(memop, 'TYPE', where)
            pack = _field(memop, 'PACK', where)
            if name == 'LOAD':
                key = (numtype, None) if pack is None else (numtype, *_args(pack, 2, where))
                code = _lookup(LOAD, key, where)
            else:
                code = _lookup(STORE, (numtype, pack), where)
            return bytes([code]) + self.memarg(x, memop, where)
        if name == 'VEC.LOAD':
            x, memop = _args(p, 2, where)
            if _field(memop, 'TYPE', where) != 'V128T':
                raise Unencodable(f'{where}: vector load of a non-vector type')
            pack = _field(memop, 'PACK', where)
            if pack is None:
                code = 0
            else:
                packtype, vext = _args(pack, 2, where)
                vname, vpayload = _ctor(vext, where)
                if vname == 'ExtLane':
                    shape, ext = _args(vpayload, 2, where)
                    code = _lookup(VLOAD_LANE, (packtype, shape, ext), where)
                elif vname == 'ExtSplat' and vpayload is None:
                    code = _lookup(VLOAD_SPLAT, packtype, where)
                elif vname == 'ExtZero' and vpayload is None:
                    code = _lookup(VLOAD_ZERO, packtype, where)
                else:
                    raise Unencodable(f'{where}: unknown vector extension {vname}')
            return _prefixed(0xFD, code) + self.memarg(x, memop, where)
        if name == 'VEC.STORE':
            x, memop = _args(p, 2, where)
            if _field(memop, 'TYPE', where) != 'V128T' or _field(memop, 'PACK', where) != 'VOID':
                raise Unencodable(f'{where}: unknown vector store')
            return _prefixed(0xFD, 11) + self.memarg(x, memop, where)
        if name in ('VEC.LOAD_LANE', 'VEC.STORE_LANE'):
            x, memop, lane = _args(p, 3, where)
            if _field(memop, 'TYPE', where) != 'V128T':
                raise Unencodable(f'{where}: lane access of a non-vector type')
            table = VLANE_LOAD if name == 'VEC.LOAD_LANE' else VLANE_STORE
            code = _lookup(table, _field(memop, 'PACK', where), where)
            return _prefixed(0xFD, code) + self.memarg(x, memop, where) + _byte(lane, where)
        if name == 'CONST':
            kind, value = _ctor(p, where)
            if kind == 'I32':
                return b'\x41' + _sleb(_signed(value, 32, where))
            if kind == 'I64':
                return b'\x42' + _sleb(_signed(value, 64, where))
            if kind == 'F32':
                return b'\x43' + struct.pack('<I', float_bits(value, 32, where))
            if kind == 'F64':
                return b'\x44' + struct.pack('<Q', float_bits(value, 64, where))
            raise Unencodable(f'{where}: unknown constant type {kind}')
        if name in ('TEST', 'COMPARE', 'BINOP'):
            kind, op = _ctor(p, where)
            table = {'TEST': TESTOP, 'COMPARE': RELOP, 'BINOP': BINOP}[name]
            return bytes([_lookup(table, (kind, op), where)])
        if name == 'UNARY':
            kind, op = _ctor(p, where)
            opname, oppayload = _ctor(op, where)
            if opname == 'ExtendS':
                return bytes([_lookup(EXTENDS, (kind, oppayload), where)])
            return bytes([_lookup(UNOP, (kind, opname), where)])
        if name == 'CONVERT':
            kind, op = _ctor(p, where)
            return _lookup(CVTOP, (kind, op), where)
        if name == 'VEC.CONST':
            vname, bits = _ctor(p, where)
            bits = _nat(bits, where)
            if vname != 'V128' or bits >= 1 << 128:
                raise Unencodable(f'{where}: invalid v128 constant')
            return _prefixed(0xFD, 12) + bits.to_bytes(16, 'little')
        if name in ('VEC.TEST', 'VEC.UNARY', 'VEC.TERNARY', 'VEC.COMPARE', 'VEC.CONVERT',
                    'VEC.SHIFT', 'VEC.BITMASK'):
            shape, op = self._vecop(p, where)
            table = {'VEC.TEST': VTEST, 'VEC.UNARY': VUNOP, 'VEC.TERNARY': VTERNOP,
                     'VEC.COMPARE': VRELOP, 'VEC.CONVERT': VCVTOP, 'VEC.SHIFT': VSHIFT,
                     'VEC.BITMASK': VBITMASK}[name]
            return _prefixed(0xFD, _lookup(table, (shape, op), where))
        if name == 'VEC.BINARY':
            shape, op = self._vecop(p, where)
            opname, oppayload = _ctor(op, where)
            if opname == 'Shuffle':
                lanes = _list(oppayload, where)
                if shape != 'I8x16' or len(lanes) != 16:
                    raise Unencodable(f'{where}: shuffle needs i8x16 and 16 lane indices')
                return _prefixed(0xFD, 13) + b''.join(_byte(l, where) for l in lanes)
            return _prefixed(0xFD, _lookup(VBINOP, (shape, opname), where))
        if name in ('VEC.TESTBITS', 'VEC.UNARYBITS', 'VEC.BINARYBITS', 'VEC.TERNARYBITS'):
            vname, op = _ctor(p, where)
            if vname != 'V128':
                raise Unencodable(f'{where}: unknown vector type {vname}')
            table = {'VEC.TESTBITS': VVTEST, 'VEC.UNARYBITS': VVUNOP,
                     'VEC.BINARYBITS': VVBINOP, 'VEC.TERNARYBITS': VVTERNOP}[name]
            return _prefixed(0xFD, _lookup(table, op, where))
        if name == 'VEC.SPLAT':
            shape, op = self._vecop(p, where)
            if op != 'Splat':
                raise Unencodable(f'{where}: unknown splat {op!r}')
            return _prefixed(0xFD, _lookup(VSPLAT, shape, where))
        if name == 'VEC.EXTRACT':
            shape, op = self._vecop(p, where)
            opname, payload = _ctor(op, where)
            if opname != 'Extract':
                raise Unencodable(f'{where}: unknown extract {opname}')
            lane, ext = _args(payload, 2, where)
            return _prefixed(0xFD, _lookup(VEXTRACT, (shape, ext), where)) + _byte(lane, where)
        if name == 'VEC.REPLACE':
            shape, op = self._vecop(p, where)
            opname, lane = _ctor(op, where)
            if opname != 'Replace':
                raise Unencodable(f'{where}: unknown replace {opname}')
            return _prefixed(0xFD, _lookup(VREPLACE, shape, where)) + _byte(lane, where)
        raise Unencodable(f'{where}: unknown instruction {name} {p!r}')

    def _ref_parts(self, value, where):
        name, payload = _ctor(value, where)
        if name != '% %':
            raise Unencodable(f'{where}: unknown reference type {name}')
        null, heap = _args(payload, 2, where)
        if null not in ('Null', 'NoNull'):
            raise Unencodable(f'{where}: unknown nullability {null!r}')
        return null == 'Null', heap

    def catch(self, value, where):
        name, p = _ctor(value, where)
        if name in ('Catch', 'CatchRef'):
            tag, label = _args(p, 2, where)
            return bytes([0 if name == 'Catch' else 1]) + u32(tag, where) + u32(label, where)
        if name in ('CatchAll', 'CatchAllRef'):
            return bytes([2 if name == 'CatchAll' else 3]) + u32(p, where)
        raise Unencodable(f'{where}: unknown catch clause {name}')

    # Module -----------------------------------------------------------------

    def module(self, m):
        where = 'module'
        if not isinstance(m, dict):
            raise Unencodable('module: expected an object')
        fields = ('TYPES', 'GLOBALS', 'TABLES', 'MEMS', 'TAGS', 'FUNCS', 'START',
                  'ELEMS', 'DATAS', 'IMPORTS', 'EXPORTS')
        if set(m) != set(fields):
            raise Unencodable(f'module: unexpected fields {sorted(m)}')
        sections = []

        def section(sid, payload):
            sections.append(bytes([sid]) + u32(len(payload), 'section size') + payload)

        types, base = [], 0
        for i, rt in enumerate(_list(m['TYPES'], 'module.TYPES')):
            encoded, count = self.rectype(rt, base, f'module.TYPES.{i}')
            types.append(encoded)
            base += count
        if types:
            section(1, _vec(types))

        imports = []
        for i, imp in enumerate(_list(m['IMPORTS'], 'module.IMPORTS')):
            w = f'module.IMPORTS.{i}'
            kind, desc = _ctor(_field(imp, 'IDESC', w), w)
            if kind == 'FuncImport':
                body = b'\x00' + u32(desc, w)
            elif kind == 'TableImport':
                body = b'\x01' + self.tabletype(desc, w)
            elif kind == 'MemImport':
                body = b'\x02' + self.memtype(desc, w)
            elif kind == 'GlobalImport':
                body = b'\x03' + self.globaltype(desc, w)
            elif kind == 'TagImport':
                body = b'\x04\x00' + u32(desc, w)
            else:
                raise Unencodable(f'{w}: unknown import kind {kind}')
            imports.append(_name(_field(imp, 'MODULENAME', w), w) + _name(_field(imp, 'ITEMNAME', w), w) + body)
        if imports:
            section(2, _vec(imports))

        funcs = _list(m['FUNCS'], 'module.FUNCS')
        if funcs:
            section(3, _vec(u32(_field(f, 'FTYPE', f'module.FUNCS.{i}'), 'FTYPE') for i, f in enumerate(funcs)))

        tables = []
        for i, t in enumerate(_list(m['TABLES'], 'module.TABLES')):
            w = f'module.TABLES.{i}'
            tables.append(b'\x40\x00' + self.tabletype(_field(t, 'TTYPE', w), w)
                          + self.expr(_field(t, 'TINIT', w), w))
        if tables:
            section(4, _vec(tables))

        mems = [self.memtype(_field(x, 'MTYPE', f'module.MEMS.{i}'), f'module.MEMS.{i}')
                for i, x in enumerate(_list(m['MEMS'], 'module.MEMS'))]
        if mems:
            section(5, _vec(mems))

        tags = [b'\x00' + u32(_field(x, 'TGTYPE', f'module.TAGS.{i}'), 'TGTYPE')
                for i, x in enumerate(_list(m['TAGS'], 'module.TAGS'))]
        if tags:
            section(13, _vec(tags))

        globals_ = []
        for i, g in enumerate(_list(m['GLOBALS'], 'module.GLOBALS')):
            w = f'module.GLOBALS.{i}'
            globals_.append(self.globaltype(_field(g, 'GTYPE', w), w) + self.expr(_field(g, 'GINIT', w), w))
        if globals_:
            section(6, _vec(globals_))

        exports = []
        for i, e in enumerate(_list(m['EXPORTS'], 'module.EXPORTS')):
            w = f'module.EXPORTS.{i}'
            kind, index = _ctor(_field(e, 'EDESC', w), w)
            code = _lookup({'FuncExport': 0, 'TableExport': 1, 'MemExport': 2,
                            'GlobalExport': 3, 'TagExport': 4}, kind, w)
            exports.append(_name(_field(e, 'NAME', w), w) + bytes([code]) + u32(index, w))
        if exports:
            section(7, _vec(exports))

        if m['START'] is not None:
            section(8, u32(_field(m['START'], 'SFUNC', 'module.START'), 'module.START'))

        elems = []
        for i, e in enumerate(_list(m['ELEMS'], 'module.ELEMS')):
            w = f'module.ELEMS.{i}'
            ref = self.reftype(_field(e, 'ETYPE', w), w)
            inits = _vec(self.expr(x, f'{w}.EINIT') for x in _list(_field(e, 'EINIT', w), w))
            mode, payload = _ctor(_field(e, 'EMODE', w), w)
            if mode == 'Passive':
                elems.append(b'\x05' + ref + inits)
            elif mode == 'Declarative':
                elems.append(b'\x07' + ref + inits)
            elif mode == 'Active':
                elems.append(b'\x06' + u32(_field(payload, 'INDEX', w), w)
                             + self.expr(_field(payload, 'OFFSET', w), w) + ref + inits)
            else:
                raise Unencodable(f'{w}: unknown element mode {mode}')
        if elems:
            section(9, _vec(elems))

        datas = []
        for i, d in enumerate(_list(m['DATAS'], 'module.DATAS')):
            w = f'module.DATAS.{i}'
            text = _field(d, 'DINIT', w)
            if not isinstance(text, str):
                raise Unencodable(f'{w}: DINIT must be text')
            # $bytes_of_text is String.toUTF8 in the translated specification.
            init = text.encode('utf-8')
            init = u32(len(init), w) + init
            mode, payload = _ctor(_field(d, 'DMODE', w), w)
            if mode == 'Passive':
                datas.append(b'\x01' + init)
            elif mode == 'Active':
                index = _nat(_field(payload, 'INDEX', w), w)
                prefix = b'\x00' if index == 0 else b'\x02' + u32(index, w)
                datas.append(prefix + self.expr(_field(payload, 'OFFSET', w), w) + init)
            else:
                raise Unencodable(f'{w}: unknown data mode {mode}')
        if datas:
            # The data count section makes memory.init/data.drop decodable.
            section(12, u32(len(datas), 'data count'))

        codes = []
        for i, f in enumerate(funcs):
            w = f'module.FUNCS.{i}'
            locals_ = [self.valtype(_field(l, 'LTYPE', w), w) for l in _list(_field(f, 'LOCALS', w), w)]
            runs = []
            for t in locals_:
                if runs and runs[-1][1] == t:
                    runs[-1][0] += 1
                else:
                    runs.append([1, t])
            body = _vec(u32(n, w) + t for n, t in runs) + self.expr(_field(f, 'BODY', w), w)
            self.code_sizes.append(len(body))
            codes.append(u32(len(body), w) + body)
        if codes:
            section(10, _vec(codes))

        if datas:
            section(11, _vec(datas))

        return b'\x00asm\x01\x00\x00\x00' + b''.join(sections)


def encode_module(module_json):
    """Return the binary encoding of a canonical-JSON module, or raise Unencodable."""
    return encode_module_details(module_json)[0]


def encode_module_details(module_json):
    """Return the binary encoding and the encoded size of each function body."""
    encoder = _Encoder()
    binary = encoder.module(module_json)
    return binary, {'code_sizes': list(encoder.code_sizes)}
