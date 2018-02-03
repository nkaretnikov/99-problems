main :: IO ()
main = do
  print $ pack ([] :: [Int])
  print $ pack ['a', 'a', 'a', 'a', 'b', 'c', 'c', 'a'
               ,'a', 'd', 'e', 'e', 'e', 'e']

pack :: Eq a => [a] -> [[a]]
pack []     = []
pack (x:xs) = go [] x xs
  where
    go :: Eq a => [a] -> a -> [a] -> [[a]]
    go acc y []     = [acc ++ [y]]
    go acc y (z:zs) =
      if y == z
      then go (acc ++ [y]) z zs
      else (acc ++ [y]) : go [] z zs
