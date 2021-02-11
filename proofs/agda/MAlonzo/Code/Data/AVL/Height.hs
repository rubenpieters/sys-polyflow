{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.AVL.Height where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Fin.Base

name6 = "Data.AVL.Height.ℕ₂"
d6 :: ()
d6 = erased
name14 = "Data.AVL.Height._⊕_"
d14 :: MAlonzo.Code.Data.Fin.Base.T6 -> Integer -> Integer
d14 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C10 -> coe v1
      MAlonzo.Code.Data.Fin.Base.C16 v3
        -> coe (addInt (coe (1 :: Integer)) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
name20 = "Data.AVL.Height.pred[_⊕_]"
d20 :: MAlonzo.Code.Data.Fin.Base.T6 -> Integer -> Integer
d20 v0 v1
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe (d14 (coe v0) (coe v2))
name28 = "Data.AVL.Height._∼_⊔_"
d28 a0 a1 a2 = ()
data T28 = C32 | C36 | C40
name48 = "Data.AVL.Height.max∼"
d48 :: Integer -> Integer -> Integer -> T28 -> T28
d48 v0 v1 v2 v3 = du48 v3
du48 :: T28 -> T28
du48 v0
  = case coe v0 of
      C32 -> coe (\ v2 -> C40) erased
      C36 -> coe (\ v2 -> C36) erased
      C40 -> coe (\ v2 -> C36) erased
      _ -> MAlonzo.RTE.mazUnreachableError
name56 = "Data.AVL.Height.∼max"
d56 :: Integer -> Integer -> Integer -> T28 -> T28
d56 v0 v1 v2 v3 = du56 v3
du56 :: T28 -> T28
du56 v0
  = case coe v0 of
      C32 -> coe (\ v2 -> C36) erased
      C36 -> coe (\ v2 -> C36) erased
      C40 -> coe (\ v2 -> C32) erased
      _ -> MAlonzo.RTE.mazUnreachableError
