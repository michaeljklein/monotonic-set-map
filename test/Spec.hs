import Lib
import Control.Monad

main :: IO ()
main = do
  passed <- runTests
  unless passed $ error "some tests did not pass"

