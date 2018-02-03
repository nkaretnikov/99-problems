main :: IO ()
main = do
  print $ elementAt [1,2,3] 2
  print $ elementAt "haskell" 5

elementAt :: [a] -> Int -> a
elementAt []     _ = error "Empty list"
elementAt _      0 = error "Invalid index"
elementAt (x:_)  1 = x
elementAt (x:xs) n = elementAt xs (n - 1)
