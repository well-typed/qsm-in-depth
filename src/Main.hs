{-# LANGUAGE ImportQualifiedPost #-}

module Main (main) where

import Test.Tasty

import UsingQD qualified

main :: IO ()
main = defaultMain $ testGroup "qsm-in-depth" [
      UsingQD.tests
    ]