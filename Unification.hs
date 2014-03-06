import Control.Applicative ((<$>), (<*>))
import Data.Char (toUpper, toLower)
import Data.List (intercalate)
import Data.Maybe (fromMaybe)

-- the types of constants
data Literal = IntLiteral Int
             | BoolLiteral Bool
    deriving Eq

instance Show Literal where
    show (IntLiteral i)  = show i
    show (BoolLiteral b) = show b

-- a first-order term
data Term = Constant Literal
          | Variable String
          | Application String [Term]

instance Show Term where
    show (Constant c)       = show c
    show (Variable v)       = map toUpper v
    show (Application f ts) = map toLower f ++ "(" ++ intercalate ", " (map show ts) ++ ")"

-- what a variable could be replaced by
type Substitution = (String, Term)


-- unification takes two terms and results in a list of substitutions, or failure
unify :: Term -> Term -> Maybe [Substitution]
-- a constant unifies with a constant only if it's the same constant, and no substitutions are needed
unify (Constant c) (Constant d)             | c == d    = Just []
                                            | otherwise = Nothing
-- a variable unifies with a term easily (V = t), provided it does not occur in a (which would give a cyclical binding)
unify (Variable v) a@(Application _ _)      | not (occurs v a)  = Just [(v, a)]
                                            | otherwise         = Nothing
unify (Variable v) t                        = Just [(v, t)]
-- the same as above, but with terms reversed
unify a@(Application _ _) (Variable v)      | not (occurs v a)  = Just [(v, a)]
                                            | otherwise         = Nothing
unify t (Variable v)                        = Just [(v, t)]
-- a function application unifies with another function application, if they are the same function, and their parameters unify
unify (Application f xs) (Application g ys) | f == g    = unifyParams xs ys
                                            | otherwise = Nothing
-- other combinations, like a constant and an application, cannot unify at all
unify _ _                                   = Nothing



occurs :: String -> Term -> Bool
occurs x (Variable v)       = x == v
occurs x (Application _ ts) = any (occurs x) ts
occurs x _                  = False



unifyParams :: [Term] -> [Term] -> Maybe [Substitution]
-- an empty list of parameters can always be unified with an empty list
unifyParams [] []         = Just []
-- otherwise, after we unify the first parameters, we have to apply the substitutions to the rest of the parameters
unifyParams (x:xs) (y:ys) | length xs /= length ys = Nothing
                          | otherwise              = let
                                subs  = unify x y
                                xs'   = map (apply (fromMaybe [] subs)) xs
                                ys'   = map (apply (fromMaybe [] subs)) ys
                                subs' = unifyParams xs' ys'
                            in (++) <$> subs <*> subs'



apply :: [Substitution] -> Term -> Term
apply s x@(Variable v)     = fromMaybe x $ lookup v s
apply s (Application f ts) = Application f (map (apply s) ts)
apply _ t                  = t



main = do
    let a = Variable "X"
        b = Variable "Y"
        c = Application "cons" [Constant (IntLiteral 2), b]
        d = Application "cons" [a, Constant (BoolLiteral False)]
        e = Application "cons" [a, d]

    -- Nothing because no finite solution exists (fails the occurs check)
    print $ unify b c

    -- X => 2, Y => cons(2, False)
    print $ unify c e
