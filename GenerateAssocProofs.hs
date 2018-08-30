{-# OPTIONS_GHC -Wall #-}
module GenerateAssocProofs where

import Data.Foldable (traverse_)
import Control.Monad.Trans.State

data Tree
    = Bla
    | Tree :++ Tree
  deriving (Eq, Ord)


instance Show Tree where
    showsPrec _ Bla = showString "Bla"
    showsPrec d (lhs :++ rhs) = showParen (d > 5)
        $ showsPrec 6 lhs
        . showString " :++ "
        . showsPrec 5 rhs

infixr 5 :++

-- | @'trees' n@ generates all trees of size n
trees :: Int -> [Tree]
trees n | n <= 1 = [Bla]
trees n =
    [ lhs :++ rhs
    | (m, p) <- divide n
    , lhs <- trees m
    , rhs <- trees p 
    ]

divide :: Int -> [(Int, Int)]
divide n = [ (m, n - m) | m <- [ 1 .. n - 1 ] ]

tailLength :: Tree -> Int
tailLength Bla           = 1
tailLength (Bla :++ rhs) = 1 + tailLength rhs
tailLength (_   :++ rhs) = tailLength rhs

haveTails :: Tree -> Tree -> Bool
haveTails lhs rhs = tailLength lhs > 1 && tailLength rhs > 1

pairs' :: Int -> [(Tree, Tree)]
pairs' n = 
    [ (lhs, rhs)
    | rhs <- trees n
    , lhs <- trees n
    , lhs /= rhs
    ]

names :: [String]
names = cycle ["as", "bs", "cs", "ds", "es", "fs", "gs"]

data Spec = Spec
    { specOp      :: ShowS -> ShowS -> ShowS
    , specParens' :: ShowS -> ShowS
    }

nameSpec :: Spec
nameSpec = Spec op parens where
    op lhs rhs = lhs . showString "++" . rhs
    parens s = showChar '[' . s . showChar ']'

propSpec :: Spec
propSpec = Spec op parens where
    op lhs rhs = lhs . showString " ++ " . rhs
    parens s = showChar '(' . s . showChar ')'

proofSpec :: Spec
proofSpec = Spec op parens where
    op lhs rhs = lhs . showString " :++ " . rhs
    parens s = showChar '(' . s . showChar ')'

specParens :: Spec -> Bool -> ShowS -> ShowS
specParens _    False = id
specParens spec True  = specParens' spec

showTree :: Spec -> Int -> Tree -> State [String] ShowS
showTree _ _ Bla = do
    (x : xs) <- get
    put xs
    return $ showString x
showTree spec d (lhs :++ rhs) = specParens spec (d > 5) <$> do
    l <- showTree spec 6 lhs
    r <- showTree spec 5 rhs
    return (specOp spec l r)

showName :: Tree -> Tree -> String
showName lhs rhs
    = evalState (showTree nameSpec 0 lhs) (repeat "xs")
    . showString "≡"
    . evalState (showTree nameSpec 0 rhs) (repeat "xs")
    $ ""

showProp :: Tree -> Tree -> String
showProp lhs rhs
    = evalState (showTree propSpec 0 lhs) names
    . showString " ≡ "
    . evalState (showTree propSpec 0 rhs) names
    $ ""

showProof :: Tree -> Tree -> String
showProof lhs rhs
    = evalState (showTree proofSpec 0 lhs) (repeat "bla")
    . showString " :≡ "
    . evalState (showTree proofSpec 0 rhs) (repeat "bla")
    $ ""

size :: Int
size = 4

printLemma :: Tree -> Tree -> IO ()
printLemma lhs rhs = do
    let name = showName lhs rhs
    let prop = showProp lhs rhs
    putStrLn $ name ++ " : ∀ {a} {A : Set a}"
    putStrLn $ "  → (" ++ unwords (take size names) ++ " : List A)"
    putStrLn $ "  → " ++ prop
    putStrLn $ name ++ " = list-solve"
    putStrLn $ "  (" ++ showProof lhs rhs ++ ")"
    putStrLn ""

main :: IO ()
main = do
    putStrLn $ "-- ASSOCIATIVITY FOR FORMULAS OF SIZE " ++ show size
    putStrLn $ take 72 (repeat '-')
    putStrLn ""
    traverse_ (uncurry printLemma) (pairs' size)
