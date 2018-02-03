data NestedList a
  = Elem a
  | List [NestedList a]

main :: IO ()
main = do
  print $ flatten (Elem 5)
  print $ flatten (List [Elem 1, List [Elem 2, List [Elem 3, Elem 4], Elem 5]])
  print $ flatten (List [] :: NestedList Int)

flatten :: NestedList a -> [a]
flatten (Elem x)      = [x]
flatten (List [])     = []
flatten (List (x:xs)) = flatten x ++ flatten (List xs)
