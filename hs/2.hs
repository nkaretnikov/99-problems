main :: IO ()
main = do
  print $ myButLast [1,2,3,4]
  print $ myButLast ['a'..'z']

myButLast :: [a] -> a
myButLast []     = error "Empty list"
myButLast [_]    = error "Not enough elements"
myButLast [x,_]  = x
myButLast (x:xs) = myButLast xs

