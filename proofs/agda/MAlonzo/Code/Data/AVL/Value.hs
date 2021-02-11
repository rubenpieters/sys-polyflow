{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.AVL.Value where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary

name36 = "Data.AVL.Value.Value"
d36 a0 a1 a2 a3 = ()
newtype T36
  = C48 (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
name44 = "Data.AVL.Value.Value.family"
d44 :: T36 -> AgdaAny -> ()
d44 = erased
name46 = "Data.AVL.Value.Value.respects"
d46 :: T36 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d46 v0
  = case coe v0 of
      C48 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name52 = "Data.AVL.Value.const"
d52 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Agda.Primitive.T4 -> () -> T36
d52 v0 v1 v2 v3 v4 = du52
du52 :: T36
du52 = coe (\ v0 v1 -> C48 v1) erased (\ v0 v1 v2 v3 -> v3)
