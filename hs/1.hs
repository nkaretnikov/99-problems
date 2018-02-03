main :: IO ()
main = do
  print $ myLast [1,2,3,4]
  print $ myLast ['x','y','z']

myLast :: [a] -> a
myLast []     = error "Empty list"
myLast [x]    = x
myLast (x:xs) = myLast xs
