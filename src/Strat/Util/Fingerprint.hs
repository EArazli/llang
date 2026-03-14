module Strat.Util.Fingerprint
  ( fingerprintBytes
  , fingerprintText
  ) where

import Data.Bits (xor)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word (Word64)
import Numeric (showHex)


fingerprintBytes :: ByteString -> Text
fingerprintBytes =
  T.pack . padHex . (`showHex` "") . hashBytes
  where
    padHex xs = replicate (16 - length xs) '0' <> xs


fingerprintText :: Text -> Text
fingerprintText = fingerprintBytes . TE.encodeUtf8


hashBytes :: ByteString -> Word64
hashBytes =
  BS.foldl' step 14695981039346656037
  where
    step acc byte =
      (acc `xor` fromIntegral byte) * 1099511628211
