-- Because this uses Haskell, and Haskell has a nice type system,
-- we don't need judgment_type at all. The type we're going to use
-- here to represent types guarantees that what we would've done
-- with judgment_type is handled. We also don't need the type_equality
-- function because Haskell can derive the correct equality.

data Type = Foo | Bar | Baz
          | Type :*: Type
          | Type :->: Type
  deriving (Eq)


-- We still need judgment_ctx (if we decide to use it) because it does
-- more than simply assure the right overall form: it also checks that
-- the variables are all distinct. So this type is only part of it.

data Context = Empty | Snoc Context String Type


not_in :: String -> Context -> Bool
not_in n Empty = True
not_in n (Snoc g n' _)
  | n == n'    = False
  | otherwise  = not_in n g


judgment_ctx :: Context -> Bool
judgment_ctx Empty        = True
judgment_ctx (Snoc g n a) = judgment_ctx g
                         && not_in n g


data Term = Pair Term Term | Split Term String Type String Type Term
          | Lam String Term | App Term Term Type
          | Var String


var_has_type :: String -> Type -> Context -> Bool
var_has_type n a Empty = False
var_has_type n a (Snoc g n' a')
  | n == n'            = a == a'
  | otherwise          = var_has_type n a g


judgment_check :: Context -> Term -> Type -> Bool
judgment_check g (Pair m n) (a :*: b)  = judgment_check g m a
                                      && judgment_check g n b

judgment_check g (Split p x a y b m) c = judgment_check g p (a :*: b)
                                      && judgment_check (Snoc (Snoc g x a)
                                                              y b)
                                                        m
                                                        c

judgment_check g (Lam x m) (a :->: b)  = judgment_check (Snoc g x a) m b

judgment_check g (App m n a) b         = judgment_check g m (a :->: b)
                                      && judgment_check g n a

judgment_check g (Var x) a             = var_has_type x a g
