import Data.List (reverse)

main :: IO ()
main = do
  print $ isPalindrome [1,2,3]
  print $ isPalindrome "madamimadam"
  print $ isPalindrome [1,2,4,8,16,8,4,2,1]

isPalindrome :: Eq a => [a] -> Bool
isPalindrome xs = reverse xs == xs
