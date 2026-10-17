import pbt.p4.UnparseGenerated

namespace Spec4Pbt.P4

/-- Render the complete `SpecTec.p4program` syntax tree as P4 source text.
    Malformed lexer payloads and constructors that lost identifier lexemes
    return an error instead of inventing source tokens. -/
def unparseProgram (program : SpecTec.p4program) : Except String String :=
  Generated.renderP4program program

end Spec4Pbt.P4
