main :: IO ()
main = do
  print $ encode "aaaabccaadeeee"
  print $ encode ([] :: [Int])

encode :: Eq a => [a] -> [(Int, a)]
encode []     = error "Empty list"
encode (x:xs) = go 0 x xs
  where
    go :: Eq a => Int -> a -> [a] -> [(Int, a)]
    go n y []     = [(n + 1, y)]
    go n y (z:zs) =
      if y == z
      then go (n + 1) z zs
      else (n + 1, y) : go 0 z zs
