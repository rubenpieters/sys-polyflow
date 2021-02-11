{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.DifferenceList where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Base

name6 = "Data.DifferenceList.DiffList"
d6 :: MAlonzo.Code.Agda.Primitive.T4 -> () -> ()
d6 = erased
name14 = "Data.DifferenceList.lift"
d14 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  ([AgdaAny] -> [AgdaAny]) ->
  ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d14 v0 v1 v2 v3 v4 = du14 v2 v3 v4
du14 ::
  ([AgdaAny] -> [AgdaAny]) ->
  ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du14 v0 v1 v2 = coe v0 (coe v1 v2)
name26 = "Data.DifferenceList.[]"
d26 ::
  MAlonzo.Code.Agda.Primitive.T4 -> () -> [AgdaAny] -> [AgdaAny]
d26 v0 v1 v2 = du26 v2
du26 :: [AgdaAny] -> [AgdaAny]
du26 v0 = coe v0
name34 = "Data.DifferenceList._∷_"
d34 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> AgdaAny -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d34 v0 v1 v2 v3 v4 = du34 v2 v3 v4
du34 ::
  AgdaAny -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du34 v0 v1 v2
  = coe (MAlonzo.Code.Agda.Builtin.List.C22 (coe v0) (coe v1 v2))
name42 = "Data.DifferenceList.[_]"
d42 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> AgdaAny -> [AgdaAny] -> [AgdaAny]
d42 v0 v1 v2 = du42 v2
du42 :: AgdaAny -> [AgdaAny] -> [AgdaAny]
du42 v0 = coe (MAlonzo.Code.Agda.Builtin.List.C22 (coe v0))
name50 = "Data.DifferenceList._++_"
d50 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  ([AgdaAny] -> [AgdaAny]) ->
  ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d50 v0 v1 v2 v3 v4 = du50 v2 v3 v4
du50 ::
  ([AgdaAny] -> [AgdaAny]) ->
  ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du50 v0 v1 v2 = coe v0 (coe v1 v2)
name62 = "Data.DifferenceList.toList"
d62 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny]
d62 v0 v1 v2 = du62 v2
du62 :: ([AgdaAny] -> [AgdaAny]) -> [AgdaAny]
du62 v0 = coe v0 MAlonzo.Code.Agda.Builtin.List.C16
name70 = "Data.DifferenceList.fromList"
d70 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d70 v0 v1 v2 = du70 v2
du70 :: [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du70 v0 = coe (MAlonzo.Code.Data.List.Base.du58 (coe v0))
name84 = "Data.DifferenceList.map"
d84 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d84 v0 v1 v2 v3 v4 v5 = du84 v4 v5
du84 ::
  (AgdaAny -> AgdaAny) ->
  ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du84 v0 v1
  = coe
      (MAlonzo.Code.Data.List.Base.du58
         (coe
            (MAlonzo.Code.Data.List.Base.du20
               (coe v0) (coe v1 MAlonzo.Code.Agda.Builtin.List.C16))))
name96 = "Data.DifferenceList.concat"
d96 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  ([[AgdaAny] -> [AgdaAny]] -> [[AgdaAny] -> [AgdaAny]]) ->
  [AgdaAny] -> [AgdaAny]
d96 v0 v1 v2 = du96 v2
du96 ::
  ([[AgdaAny] -> [AgdaAny]] -> [[AgdaAny] -> [AgdaAny]]) ->
  [AgdaAny] -> [AgdaAny]
du96 v0 = coe du108 (coe v0 MAlonzo.Code.Agda.Builtin.List.C16)
name108 = "Data.DifferenceList._.concat'"
d108 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  ([[AgdaAny] -> [AgdaAny]] -> [[AgdaAny] -> [AgdaAny]]) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> [[AgdaAny] -> [AgdaAny]] -> [AgdaAny] -> [AgdaAny]
d108 v0 v1 v2 v3 v4 = du108
du108 :: [[AgdaAny] -> [AgdaAny]] -> [AgdaAny] -> [AgdaAny]
du108
  = coe
      (MAlonzo.Code.Data.List.Base.du202
         (coe (\ v0 v1 v2 -> coe v0 (coe v1 v2))) (coe (\ v0 -> v0)))
name114 = "Data.DifferenceList.take"
d114 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> Integer -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d114 v0 v1 v2 v3 v4 = du114 v2 v3 v4
du114 ::
  Integer -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du114 v0 v1 v2
  = coe (MAlonzo.Code.Data.List.Base.du456 (coe v0) (coe v1 v2))
name122 = "Data.DifferenceList.drop"
d122 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> Integer -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d122 v0 v1 v2 v3 v4 = du122 v2 v3 v4
du122 ::
  Integer -> ([AgdaAny] -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du122 v0 v1 v2
  = coe (MAlonzo.Code.Data.List.Base.du468 (coe v0) (coe v1 v2))
