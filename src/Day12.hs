module Day12 where

-- http://benl.ouroborus.net/papers/lambda-dsim/lambda-dsim-20160328.pdf

import Data.List (find)

data Term
  = Var String
  | Lam [(String, Term)] String Term
  | App Term Term

instance Show Term where
  show (Var name) = name
  show (Lam substs name body) =
    let bodyStr = unwords
          [ "(\\" ++ name
          , show body ++ ")"
          ]
    in if null substs
       then bodyStr
       else unwords
         [ "{"
         , foldr
             (\(name', tm) str -> name' ++ " = " ++ show tm ++ ", " ++ str)
             ""
             substs
         , "} |>"
         , bodyStr
         ]
  show (App tm1 tm2) =
    let tm2str = case tm2 of
          Var _ -> show tm2
          _ -> "(" ++ show tm2 ++ ")"
    in unwords [show tm1, tm2str]

-- Joel: this is the opposite of what I would expect
value :: Term -> Bool
value (Lam _ _ _) = True
value _ = False

done :: Term -> Bool
done (Var _) = True
done (App e1 _)
  | done e1 && not (value e1) = True
done e
  | value e = True
done _ = False

reduce :: Term -> Term
-- EsReduce
reduce (App (Lam substs name e1) e2)
  | done e2 = subst ((name, e2):substs) e1
reduce (App e1 e2)
  | value e1
reduce t = t

subst :: [(String, Term)] -> Term -> Term
subst substs tm = case tm of
  Var x -> case find (\(name, _) -> name == x) substs of
    Just (_, tm') -> tm'
    Nothing -> tm

  -- 2.2 nested substitutions:
  -- "To combine the outer substitution with the inner one, we first apply the
  -- outer subsitution to each binding of the inner one, then append the outer
  -- substitution to the left (here we use the opposite direction, so right. in
  -- any case, applied after.) of that result."
  Lam innerSubsts x body ->
    let mappedInnerSubsts = map
          (\(name, substTm) -> (name, subst substs substTm))
          innerSubsts
    in Lam (mappedInnerSubsts ++ substs) x body

  App tm1 tm2 -> App (subst substs tm1) (subst substs tm2)

main :: IO ()
main = do
  let ex1 = App
        (App
          (Lam [] "x"
            (Lam [] "y"
              (App
                (App (Var "add") (Var "x"))
                (App (Lam [] "z" (Var "z")) (Var "y")))))
          (App (Var "succ") (Var "y")))
        (Var "five")
      ex1expected = App
        (App (Var "add")
             (App (Var "succ") (Var "y")))
        (Var "five")
  print (reduce ex1)
  print (reduce ex1expected)
