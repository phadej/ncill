module GenerateAssocProofs where

import Data.List
import Data.Foldable (traverse_, for_)

data Tree
    = Bla
    | Nil
    | Tree :++ Tree
  deriving (Eq, Ord)

{-
size :: Tree -> Int
size Nil = 0
size Bla = 1
size (lhs :++ rhs) = size lhs + size rhs
-}

hasNil :: Tree -> Bool
hasNil Bla           = False
hasNil Nil           = True
hasNil (lhs :++ rhs) = hasNil lhs || hasNil rhs

instance Show Tree where
    showsPrec _ Bla = showString "Bla"
    showsPrec _ Nil = showString "Nil"
    showsPrec d (lhs :++ rhs) = showParen (d > 5)
        $ showsPrec 6 lhs
        . showString " :++ "
        . showsPrec 5 rhs

-- | App
(+++) :: Tree -> Tree -> Tree
(+++) Nil ys = ys
(+++) xs  ys = xs :++ ys

infixr 5 +++, :++

-- | @'trees' n@ generates all trees of size n
trees :: Int -> [Tree]
trees 0 = [Nil]
trees 1 = [Bla, Bla +++ Nil]
trees n =
    [ lhs +++ rhs
    | (m, p) <- divide n
    , lhs <- trees m
    , rhs <- trees p 
    ]

divide :: Int -> [(Int, Int)]
divide n = [ (m, n - m) | m <- [ 1 .. n - 1 ] ]

trees' :: Int -> [Tree]
trees' = filter (not . hasNil) . trees

tailLength :: Tree -> Maybe Int
tailLength Bla           = Just 1
tailLength Nil           = Nothing
tailLength (Bla :++ rhs) = (1 +) <$> tailLength rhs
tailLength (_   :++ rhs) = tailLength rhs

haveTails :: Tree -> Tree -> Bool
haveTails lhs rhs 
    | Just n <- tailLength lhs
    , Just m <- tailLength rhs = n > 1 && m > 1
    | otherwise = False

pairs' :: Int -> [(Tree, Tree)]
pairs' n = 
    [ (lhs, rhs)
    | rhs <- trees' n
    , lhs <- trees' n
    , lhs /= rhs
    , not (haveTails lhs rhs)
    ]

names :: [String]
names = ["as", "bs", "cs", "ds", "es", "fs", "gs"]

printLemma :: Tree -> Tree -> IO ()
printLemma lhs rhs = do
    print lhs
    print rhs

main :: IO ()
main = traverse_ (uncurry printLemma) (pairs' 3)
