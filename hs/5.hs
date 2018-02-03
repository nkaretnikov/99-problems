main :: IO ()
main = do
  print $ myReverse "A man, a plan, a canal, panama!"
  print $ myReverse [1,2,3,4]

myReverse :: [a] -> [a]
myReverse []     = []
myReverse (x:xs) = myReverse xs ++ [x]
