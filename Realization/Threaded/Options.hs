module Realization.Threaded.Options where

data TranslationOptions = TranslationOptions { dedicatedErrorState :: Bool
                                             , safeSteps :: Bool
                                             , defaultInit :: Bool
                                             , bitPrecise :: Bool
                                             , showHelp :: Bool
                                             }
