import STLC.Syntax
import Std.Internal.Parsec.String

open Syntax
open Std Internal Parsec String

namespace Parser

partial def parseTy : Parser Ty := do
  let lhs ← parsePrimaryTy
  ws
  (do
    _ ← pstring "=>"
    ws
    let rhs ← parseTy
    pure (.arr lhs rhs)
  ) <|> pure lhs
where
  parsePrimaryTy : Parser Ty :=
    (pstring "T" *> pure .base) <|>
    (pstring "(" *> parseTy <* pstring ")")

partial def parseRaw : Parser Raw :=
  parseAbs <|> parseApp
where
  -- Parsers for names (variables)
  parseName : Parser String := do
    let s ← many1 (satisfy fun c => c.isAlphanum || c == '_')
    pure s.toList.asString

  -- λ(x : Ty). Raw
  parseAbs : Parser Raw := do
    _ ← (pstring "λ" <|> pstring "\\")
    _ ← pstring "("
    let name ← parseName
    _ <- ws *> pstring ":" <* ws
    let ty ← parseTy
    _ ← pstring ")"
    _ <- ws *> pstring "." <* ws
    let body ← parseRaw
    pure (.abs name ty body)

  -- Handle applications (left-associative)
  parseApp : Parser Raw := do
    let first ← parseAtom
    let rest ← many (ws *> parseAtom)
    pure (rest.foldl .app first)

  -- Variables or nested parens
  parseAtom : Parser Raw :=
    (pstring "(" *> ws *> parseRaw <* ws <* pstring ")") <|>
    (.var <$> parseName)
