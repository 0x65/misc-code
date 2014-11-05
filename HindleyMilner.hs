import Control.Monad
import Control.Monad.State
import Data.Maybe

import qualified Data.Map as Map
import qualified Data.Set as Set

-- the lambda calculus with let expressions, and literals for easier use
data Expr = EVariable String
          | EApplication Expr Expr
          | EAbstraction String Expr
          | ELet String Expr Expr
          | ELiteral Literal
    deriving (Show, Eq)

data Literal = LInteger Integer
             | LBoolean Bool
             | LString String
    deriving Eq

instance Show Literal where
    show (LInteger _) = "int"
    show (LBoolean _) = "bool"
    show (LString _)  = "string"

-- a monotype is a variable standing for a monotype, or a named application of types
-- examples of applications are "int" (taking 0 types) or "function" (taking 2 types)
data Monotype = TVariable String
              | TApplication String [Monotype]
    deriving (Show, Eq)

-- a polytype is a variable bound by quantifiers, i.e. forall a b. X
-- having the inner type be a monotype ensures that polytypes are only ever present at the outermost level of a type
data Polytype = Polytype [String] Monotype

-- a context is set of assumptions that assigns each variable in the expression language a type
newtype Context = Context (Map.Map String Polytype)

-- unification constraints are a mapping from a type variable to a type, stating that the two are equivalent
type Constraints = Map.Map String Monotype

-- the class of things that have variables. we can replace each variable
-- with the type it is constrained to be, and get unbound variables
class Variable a where
    substitute :: Constraints -> a -> a
    free :: a -> Set.Set String

instance Variable Monotype where
    substitute cs (TVariable x)       = fromMaybe (TVariable x) (Map.lookup x cs)
    substitute cs (TApplication d ts) = TApplication d (map (substitute cs) ts)
    free (TVariable a)                = Set.singleton a
    free (TApplication _ ts)          = foldr (Set.union . free) Set.empty ts

instance Variable Polytype where
    substitute cs (Polytype as s) = Polytype as (substitute (foldr Map.delete cs as) s)
    free (Polytype as s)          = Set.difference (free s) (Set.fromList as)

instance Variable Context where
    substitute cs (Context g) = Context $ Map.map (substitute cs) g
    free (Context g)          = foldr (Set.union . free) Set.empty (Map.elems g)

compose :: Constraints -> Constraints -> Constraints
compose x y = Map.map (substitute x) y `Map.union` x

-- we use state to let us generate unique variable names
type Infer = State String

newVariable :: Infer Monotype
newVariable = get >>= \unused ->
    case unused of
        (x:xs)  -> put xs >> return (TVariable [x])
        []      -> error "Use less variables, dingus"

-- a polytype is instantiated (or specialized) by replacing all of the
-- quantified variables by arbitrary monotypes. for example, a polytype
-- forall a b. a -> b can be specialized to A -> B, where A and B refer
-- to a specific type
instantiate :: Polytype -> Infer Monotype
instantiate (Polytype as s) = do
    bs <- mapM (const newVariable) as
    return $ substitute (Map.fromList (zip as bs)) s

-- a monotype is generalized in the opposite direction from instantiation.
-- that is, a type A -> B can be generalized to forall a b. a -> b, if
-- A and B are not bound by the context (to prevent overgeneralization).
-- the free variables of the context are the ones bound in the term.
generalize :: Context -> Monotype -> Polytype
generalize c t = Polytype (Set.toList (Set.difference (free t) (free c))) t

-- construct a constraint that a variable must be a particular type
-- we perform an occurs check to prevent cyclical bindings, e.g. X = A -> X
constrain :: String -> Monotype -> Constraints
constrain a t  | Set.member a (free t) = error $ "Occurs check fails in binding " ++ a ++ " to " ++ show t
               | t == TVariable a      = Map.empty
               | otherwise             = Map.singleton a t

-- unification attempts to make two monotypes equal by finding
-- legal substitutions for type variables
unify :: Monotype -> Monotype -> Infer Constraints
-- if one side is a variable, we can just substitute it with the other type
unify (TVariable x) t = return $ constrain x t
unify t (TVariable x) = return $ constrain x t
-- if both are function applications, they are equal iff all their parameters unify
unify (TApplication n xs) (TApplication m ys) = do
        when (length xs /= length ys) $ 
            error $ "Applications of " ++ n ++ " and " ++ m ++ " have a different number of parameters"
        constraints <- unifyParams (zip xs ys) [Map.empty]
        return $ foldr compose Map.empty constraints
    where unifyParams [] cs                = return cs
          unifyParams ((x, y):ps) cs@(c:_) = do
            c' <- unify (substitute c x) (substitute c y)
            unifyParams ps (c':cs)

-- given a set of assumptions, we can infer the monotype of an expr
-- by constraining type variables in it. this is algorithm w.
infer' :: Context -> Expr -> Infer (Constraints, Monotype)
-- a literal is just whatever type it is
infer' _ (ELiteral l)                   = return (Map.empty, TApplication (show l) [])
-- if x has polytype T in the context, and t is a monotype instantiated from T,
-- then x has monotype t
infer' (Context g) (EVariable x)        = case Map.lookup x g of
    Just t  -> liftM ((,) Map.empty) (instantiate t)
    Nothing -> error $ "Unbound variable " ++ x
-- if we assume x has monotype a, and that allows us to infer that y has monotype b,
-- then a function lambda x. y has monotype a -> b
infer' (Context g) (EAbstraction x y)   = do
    a <- newVariable
    let newContext = Context (Map.insert x (Polytype [] a) g)
    (constraints, b) <- infer' newContext y
    return (constraints, TApplication "function" [substitute constraints a, b])
-- if x has monotype a, and y has monotype a -> c for some unbound monotype c,
-- then the application of x to y has monotype c
infer' context (EApplication y x)       = do
    c <- newVariable
    (s, b) <- infer' context y
    (s', a) <- infer' (substitute s context) x
    s'' <- unify (substitute s' b) (TApplication "function" [a, c])
    return (foldr compose Map.empty [s, s', s''], substitute s'' c)
-- if x has monotype a, and if we assume y has a generalized polytype T,
-- and our assumption allows us to infer that z has monotype c, 
-- then let y = x in z has type c
infer' env@(Context g) (ELet y x z)      = do
    (s, a) <- infer' env x
    let t          = generalize (substitute s env) a
        newContext = Context (Map.insert y t g)
    (s', c) <- infer' (substitute s newContext) z
    return (compose s s', c)

infer :: Expr -> Monotype
infer e = let (s, t) = evalState (infer' (Context Map.empty) e) ['A'..'Z'] in substitute s t
