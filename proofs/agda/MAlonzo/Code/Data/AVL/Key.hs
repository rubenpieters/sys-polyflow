{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.AVL.Key where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict

name76 = "Data.AVL.Key.Key⁺"
d76 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 -> ()
d76 = erased
name80 = "Data.AVL.Key._._<⁺_"
d80 a0 a1 a2 a3 a4 a5 = ()
name88 = "Data.AVL.Key._<_<_"
d88 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  AgdaAny -> MAlonzo.Code.Data.Maybe.Base.T22 -> ()
d88 = erased
name98 = "Data.AVL.Key.⊥⁺<[_]<⊤⁺"
d98 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d98 v0 v1 = du98
du98 :: MAlonzo.Code.Agda.Builtin.Sigma.T14
du98
  = coe
      (MAlonzo.Code.Agda.Builtin.Sigma.C32
         (coe
            (\ v0 v1 v2 ->
               MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26 v2)
            erased erased
            (coe
               (\ v0 ->
                  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C24)
               erased))
         (coe
            (\ v0 ->
               MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
            erased))
name108 = "Data.AVL.Key.trans⁺"
d108 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
d108 v0 v1 v2 v3 v4 v5 v6 = du108 v3 v4 v5 v6
du108 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
du108 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du162
      (MAlonzo.Code.Relation.Binary.d1224
         (coe (MAlonzo.Code.Relation.Binary.d1290 (coe v0))))
      v1 v2 v3
