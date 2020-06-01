module Ast where

import Data.NonEmpty (NonEmpty)

type Expr = NonEmpty Array String

data Step
    = Action Expr
    | Choice Expr (NonEmpty Array AST)
    | Question Expr AST AST
    | Assertion Expr

-- | Struct is the main logic object. It represents
-- | the diagram as an abstract syntax tree.
data AST = Box Step AST | End

empty :: AST
empty = End

insertStep :: AST -> Step -> AST
insertStep End s = Box s End
insertStep box step = Box step box