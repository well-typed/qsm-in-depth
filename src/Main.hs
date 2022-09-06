{-# LANGUAGE ImportQualifiedPost #-}

module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Version1 qualified
import Version2 qualified

main :: IO ()
main = defaultMain $ testGroup "qsm-in-depth" [
      testGroup "Version1" [
          testProperty "sequential" $
            Version1.prop_sequential tmpDir
        , testProperty "sequential'" $
            Version1.prop_sequential' tmpDir
        , testCase "labelledExamples" $
            Version1.showLabelledExamples Nothing
        ]
    , testGroup "Version2" [
          testProperty "sequential" $
            Version2.prop_sequential tmpDir
        , testCase "labelledExamples" $
            Version2.showLabelledExamples Nothing
        ]
    ]
  where
    tmpDir :: FilePath
    tmpDir = "tmp"