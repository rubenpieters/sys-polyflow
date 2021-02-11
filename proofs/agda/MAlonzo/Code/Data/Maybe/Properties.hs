{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.Maybe.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Maybe.Relation.Unary.All
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary

name22 = "Data.Maybe.Properties.just-injective"
d22 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d22 = erased
name24 = "Data.Maybe.Properties.≡-dec"
d24 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
d24 v0 v1 v2 v3 v4 = du24 v2 v3 v4
du24 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
du24 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Maybe.Base.C28 v3
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v4 -> coe v0 v3 v4
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe (\ v4 -> MAlonzo.Code.Relation.Nullary.C26) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Maybe.Base.C30
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v3
               -> coe (\ v4 -> MAlonzo.Code.Relation.Nullary.C26) erased
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe (MAlonzo.Code.Relation.Nullary.C22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name60 = "Data.Maybe.Properties.map-id"
d60 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d60 = erased
name70 = "Data.Maybe.Properties.map-id₂"
d70 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Relation.Unary.All.T18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d70 = erased
name80 = "Data.Maybe.Properties.map-<∣>-commute"
d80 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d80 = erased
name96 = "Data.Maybe.Properties.map-cong"
d96 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d96 = erased
name112 = "Data.Maybe.Properties.map-cong₂"
d112 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Relation.Unary.All.T18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d112 = erased
name120 = "Data.Maybe.Properties.map-compose"
d120 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d120 = erased
name136 = "Data.Maybe.Properties.maybe-map"
d136 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (MAlonzo.Code.Data.Maybe.Base.T22 -> ()) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d136 = erased
name160 = "Data.Maybe.Properties.maybe′-map"
d160 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d160 = erased
name184 = "Data.Maybe.Properties._._.Associative"
d184 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (MAlonzo.Code.Data.Maybe.Base.T22 ->
   MAlonzo.Code.Data.Maybe.Base.T22 ->
   MAlonzo.Code.Data.Maybe.Base.T22) ->
  ()
d184 = erased
name200 = "Data.Maybe.Properties._._.Identity"
d200 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  (MAlonzo.Code.Data.Maybe.Base.T22 ->
   MAlonzo.Code.Data.Maybe.Base.T22 ->
   MAlonzo.Code.Data.Maybe.Base.T22) ->
  ()
d200 = erased
name212 = "Data.Maybe.Properties._._.LeftIdentity"
d212 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  (MAlonzo.Code.Data.Maybe.Base.T22 ->
   MAlonzo.Code.Data.Maybe.Base.T22 ->
   MAlonzo.Code.Data.Maybe.Base.T22) ->
  ()
d212 = erased
name224 = "Data.Maybe.Properties._._.RightIdentity"
d224 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  (MAlonzo.Code.Data.Maybe.Base.T22 ->
   MAlonzo.Code.Data.Maybe.Base.T22 ->
   MAlonzo.Code.Data.Maybe.Base.T22) ->
  ()
d224 = erased
name240 = "Data.Maybe.Properties._.<∣>-assoc"
d240 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d240 = erased
name252 = "Data.Maybe.Properties._.<∣>-identityˡ"
d252 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d252 = erased
name256 = "Data.Maybe.Properties._.<∣>-identityʳ"
d256 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d256 = erased
name260 = "Data.Maybe.Properties._.<∣>-identity"
d260 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d260 v0 v1 = du260
du260 :: MAlonzo.Code.Agda.Builtin.Sigma.T14
du260 = coe (MAlonzo.Code.Agda.Builtin.Sigma.C32 erased erased)
name296 = "Data.Maybe.Properties._._.IsMagma"
d296 a0 a1 a2 = ()
name298 = "Data.Maybe.Properties._._.IsMonoid"
d298 a0 a1 a2 a3 = ()
name306 = "Data.Maybe.Properties._._.IsSemigroup"
d306 a0 a1 a2 = ()
name589 = "Data.Maybe.Properties..absurdlambda"
d589 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Data.Empty.T4
d589 = erased
name729 = "Data.Maybe.Properties..absurdlambda"
d729 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Data.Empty.T4
d729 = erased
name1436 = "Data.Maybe.Properties._.<∣>-isMagma"
d1436 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Algebra.Structures.T84
d1436 v0 v1 = du1436
du1436 :: MAlonzo.Code.Algebra.Structures.T84
du1436
  = coe
      (MAlonzo.Code.Algebra.Structures.C277
         (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du70)
         erased)
name1438 = "Data.Maybe.Properties._.<∣>-isSemigroup"
d1438 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Algebra.Structures.T118
d1438 v0 v1 = du1438
du1438 :: MAlonzo.Code.Algebra.Structures.T118
du1438
  = coe (MAlonzo.Code.Algebra.Structures.C781 (coe du1436) erased)
name1440 = "Data.Maybe.Properties._.<∣>-isMonoid"
d1440 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Algebra.Structures.T268
d1440 v0 v1 = du1440
du1440 :: MAlonzo.Code.Algebra.Structures.T268
du1440
  = coe
      (MAlonzo.Code.Algebra.Structures.C1873 (coe du1438) (coe du260))
name1442 = "Data.Maybe.Properties._.<∣>-semigroup"
d1442 ::
  MAlonzo.Code.Agda.Primitive.T4 -> () -> MAlonzo.Code.Algebra.T76
d1442 v0 v1 = du1442
du1442 :: MAlonzo.Code.Algebra.T76
du1442
  = coe
      (\ v0 v1 v2 v3 -> MAlonzo.Code.Algebra.C285 v2 v3) erased erased
      MAlonzo.Code.Data.Maybe.Base.du98 du1438
name1444 = "Data.Maybe.Properties._.<∣>-monoid"
d1444 ::
  MAlonzo.Code.Agda.Primitive.T4 -> () -> MAlonzo.Code.Algebra.T344
d1444 v0 v1 = du1444
du1444 :: MAlonzo.Code.Algebra.T344
du1444
  = coe
      (\ v0 v1 v2 v3 v4 -> MAlonzo.Code.Algebra.C1365 v2 v3 v4) erased
      erased MAlonzo.Code.Data.Maybe.Base.du98
      MAlonzo.Code.Data.Maybe.Base.C30 du1440
