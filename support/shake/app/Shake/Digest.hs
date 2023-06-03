{-# LANGUAGE BlockArguments, GeneralizedNewtypeDeriving, TypeFamilies #-}

-- | Take the
module Shake.Digest (digestRules, getFileDigest) where

import qualified Data.ByteString.Lazy as LazyBS
import Data.Digest.Pure.SHA
import Data.Typeable

import Development.Shake.Classes (Hashable, Binary, NFData)
import Development.Shake

newtype FileDigest = FileDigest FilePath
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult FileDigest = String

-- | Shake rules required for compiling KaTeX equations.
digestRules :: Rules ()
digestRules = versioned 1 do
  _ <- addOracle \(FileDigest f) -> do
    need [f]
    take 8 . showDigest . sha256 <$> liftIO (LazyBS.readFile f)
  pure ()

-- | Get parsed preamble
getFileDigest :: FilePath -> Action String
getFileDigest = askOracle . FileDigest
