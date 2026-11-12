module WasmJson (renderModule) where

import WasmGenerator (BlockType (..), Function (..), Instr (..), Signature (..), WasmModule (..))

array :: (a -> ShowS) -> [a] -> ShowS
array render values = showChar '[' . elements values . showChar ']'
  where
    elements [] = id
    elements [value] = render value
    elements (value : rest) = render value . showChar ',' . elements rest

valueType :: ShowS
valueType = showString "{\"NumT\":\"I32T\"}"

signature :: Signature -> ShowS
signature (Signature parameters results) =
  showString "{\"RecT\":[{\"SubT\":[\"Final\",[],{\"DefFuncT\":{\"FuncT\":["
  . array (const valueType) (replicate parameters ()) . showChar ','
  . array (const valueType) (replicate results ()) . showString "]}}]}]}"

blockType :: BlockType -> ShowS
blockType block = case block of
  EmptyBlock -> showString "{\"ValBlockType\":null}"
  ValueBlock -> showString "{\"ValBlockType\":" . valueType . showChar '}'
  TypeBlock index -> showString "{\"VarBlockType\":" . shows index . showChar '}'

instruction :: Instr -> ShowS
instruction item = case item of
  IConst number -> showString "{\"CONST\":{\"I32\":" . shows number . showString "}}"
  ILocalGet index -> showString "{\"LOCAL.GET\":" . shows index . showChar '}'
  ILocalSet index -> showString "{\"LOCAL.SET\":" . shows index . showChar '}'
  ILocalTee index -> showString "{\"LOCAL.TEE\":" . shows index . showChar '}'
  IAdd -> showString "{\"BINOP\":{\"I32\":\"IAdd\"}}"
  ISub -> showString "{\"BINOP\":{\"I32\":\"ISub\"}}"
  IMul -> showString "{\"BINOP\":{\"I32\":\"IMul\"}}"
  INop -> showString "\"NOP\""
  IDrop -> showString "\"DROP\""
  IBlock block body -> showString "{\"BLOCK\":[" . blockType block . showChar ','
    . array instruction body . showString "]}"
  ILoop block body -> showString "{\"LOOP\":[" . blockType block . showChar ','
    . array instruction body . showString "]}"
  IIf block yes no -> showString "{\"IF % % ELSE %\":[" . blockType block . showChar ','
    . array instruction yes . showChar ',' . array instruction no . showString "]}"
  ICall index -> showString "{\"CALL\":" . shows index . showChar '}'

local :: () -> ShowS
local _ = showString "{\"LTYPE\":{\"NumT\":\"I32T\"}}"

function :: Function -> ShowS
function (FunctionBody index locals body) =
  showString "{\"FTYPE\":" . shows index
  . showString ",\"LOCALS\":" . array local (replicate locals ())
  . showString ",\"BODY\":" . array instruction body . showChar '}'

export :: (Int, Int) -> ShowS
export (position, target) = showString "{\"NAME\":"
  . array (shows . fromEnum) ('f' : show position)
  . showString ",\"EDESC\":{\"FuncExport\":" . shows target . showString "}}"

startFunction :: Maybe Int -> ShowS
startFunction Nothing = showString "null"
startFunction (Just index) = showString "{\"SFUNC\":" . shows index . showChar '}'

renderModule :: WasmModule -> String
renderModule (ConstructedModule signatures functions exports start) =
  (showString "{\"TYPES\":" . array signature signatures
  . showString ",\"GLOBALS\":[],\"TABLES\":[],\"MEMS\":[],\"TAGS\":[],\"FUNCS\":"
  . array function functions . showString ",\"START\":" . startFunction start
  . showString ",\"ELEMS\":[],\"DATAS\":[],\"IMPORTS\":[],\"EXPORTS\":"
  . array export (zip [0 ..] exports) . showChar '}') ""
