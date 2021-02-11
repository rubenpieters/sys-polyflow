{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Maybe.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary
import qualified MAlonzo.Code.Relation.Nullary.Decidable

name20 = "Relation.Binary.Construct.Add.Supremum.NonStrict._≤⁺_"
d20 a0 a1 a2 a3 a4 a5 = ()
data T20 = C26 AgdaAny | C30
name36
  = "Relation.Binary.Construct.Add.Supremum.NonStrict.[≤]-injective"
d36 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> T20 -> AgdaAny
d36 v0 v1 v2 v3 v4 v5 v6 = du36 v6
du36 :: T20 -> AgdaAny
du36 v0
  = case coe v0 of
      C26 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name40
  = "Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-trans"
d40 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> T20 -> T20 -> T20
d40 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du40 v4 v5 v6 v7 v8 v9
du40 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> T20 -> T20 -> T20
du40 v0 v1 v2 v3 v4 v5
  = let v6 = seq (coe v5) (coe (\ v6 -> C30) erased) in
    case coe v4 of
      C26 v9
        -> case coe v5 of
             C26 v12
               -> case coe v1 of
                    MAlonzo.Code.Data.Maybe.Base.C28 v13
                      -> case coe v2 of
                           MAlonzo.Code.Data.Maybe.Base.C28 v14
                             -> case coe v3 of
                                  MAlonzo.Code.Data.Maybe.Base.C28 v15
                                    -> coe
                                         (\ v16 v17 v18 -> C26 v18) erased erased
                                         (coe v0 v13 v14 v15 v9 v12)
                                  _ -> coe v6
                           _ -> coe v6
                    _ -> coe v6
             C30 -> coe (\ v11 -> C30) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> coe v6
name54
  = "Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-maximum"
d54 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> T20
d54 v0 v1 v2 v3 = du54
du54 :: MAlonzo.Code.Data.Maybe.Base.T22 -> T20
du54 = coe (\ v0 -> C30)
name56 = "Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-dec"
d56 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
d56 v0 v1 v2 v3 v4 v5 v6 = du56 v4 v5 v6
du56 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
du56 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Maybe.Base.C28 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Maybe.Base.C28 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.du24
                    (coe (\ v5 v6 v7 -> C26 v7) erased erased) du36 (coe v0 v4 v3)
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe (\ v4 -> MAlonzo.Code.Relation.Nullary.C26) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Maybe.Base.C30
        -> coe
             (MAlonzo.Code.Relation.Nullary.C22 (coe (\ v3 -> C30) erased))
      _ -> MAlonzo.RTE.mazUnreachableError
name72
  = "Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-total"
d72 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T30) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> MAlonzo.Code.Data.Sum.Base.T30
d72 v0 v1 v2 v3 v4 v5 v6 = du72 v4 v5 v6
du72 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T30) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> MAlonzo.Code.Data.Sum.Base.T30
du72 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Maybe.Base.C28 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Maybe.Base.C28 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.du74
                    (coe (\ v5 v6 v7 -> C26 v7) erased erased)
                    (coe (\ v5 v6 v7 -> C26 v7) erased erased) (coe v0 v4 v3)
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe (MAlonzo.Code.Data.Sum.Base.C42 (coe (\ v4 -> C30) erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Maybe.Base.C30
        -> coe (MAlonzo.Code.Data.Sum.Base.C38 (coe (\ v3 -> C30) erased))
      _ -> MAlonzo.RTE.mazUnreachableError
name88
  = "Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-irrelevant"
d88 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  T20 -> T20 -> MAlonzo.Code.Agda.Builtin.Equality.T12
d88 = erased
name100
  = "Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-reflexive-≡"
d100 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 -> T20
d100 v0 v1 v2 v3 v4 v5 v6 v7 = du100 v4 v5
du100 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> T20
du100 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Maybe.Base.C28 v2
        -> coe (\ v3 v4 v5 -> C26 v5) erased erased (coe v0 v2 v2 erased)
      MAlonzo.Code.Data.Maybe.Base.C30 -> coe (\ v2 -> C30) erased
      _ -> MAlonzo.RTE.mazUnreachableError
name108
  = "Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-antisym-≡"
d108 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  T20 -> T20 -> MAlonzo.Code.Agda.Builtin.Equality.T12
d108 = erased
name130
  = "Relation.Binary.Construct.Add.Supremum.NonStrict._._._≈∙_"
d130 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name160
  = "Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-reflexive"
d160 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  T20
d160 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du160 v6 v7 v8 v9
du160 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  T20
du160 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C22
        -> coe (\ v4 -> C30) erased
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C28 v6
        -> case coe v1 of
             MAlonzo.Code.Data.Maybe.Base.C28 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Maybe.Base.C28 v8
                      -> coe (\ v9 v10 v11 -> C26 v11) erased erased (coe v0 v7 v8 v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name168
  = "Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-antisym"
d168 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  T20 ->
  T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
d168 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du168 v6 v7 v8 v9 v10
du168 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  T20 ->
  T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
du168 v0 v1 v2 v3 v4
  = case coe v3 of
      C26 v7
        -> case coe v4 of
             C26 v10
               -> case coe v1 of
                    MAlonzo.Code.Data.Maybe.Base.C28 v11
                      -> case coe v2 of
                           MAlonzo.Code.Data.Maybe.Base.C28 v12
                             -> coe
                                  (\ v13 v14 v15 ->
                                     MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C28
                                       v15)
                                  erased erased (coe v0 v11 v12 v7 v10)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C30
        -> coe
             (seq
                (coe v1)
                (coe
                   (seq
                      (coe v4)
                      (coe
                         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C22))))
      _ -> MAlonzo.RTE.mazUnreachableError
name178
  = "Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-isPreorder-≡"
d178 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.T16
d178 v0 v1 v2 v3 v4 = du178 v4
du178 ::
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.T16
du178 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C17
         (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du70)
         (coe
            (\ v1 v2 v3 ->
               du100 (coe (MAlonzo.Code.Relation.Binary.d38 (coe v0))) v1))
         (coe (du40 (coe (MAlonzo.Code.Relation.Binary.d40 (coe v0))))))
name212
  = "Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-isPartialOrder-≡"
d212 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T256 ->
  MAlonzo.Code.Relation.Binary.T256
d212 v0 v1 v2 v3 v4 = du212 v4
du212 ::
  MAlonzo.Code.Relation.Binary.T256 ->
  MAlonzo.Code.Relation.Binary.T256
du212 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C1639
         (coe (du178 (coe (MAlonzo.Code.Relation.Binary.d274 (coe v0)))))
         erased)
name250
  = "Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-isDecPartialOrder-≡"
d250 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T378 ->
  MAlonzo.Code.Relation.Binary.T378
d250 v0 v1 v2 v3 v4 = du250 v4
du250 ::
  MAlonzo.Code.Relation.Binary.T378 ->
  MAlonzo.Code.Relation.Binary.T378
du250 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C2295
         (coe (du212 (coe (MAlonzo.Code.Relation.Binary.d398 (coe v0)))))
         (coe
            (MAlonzo.Code.Data.Maybe.Properties.du24
               (coe (MAlonzo.Code.Relation.Binary.d400 (coe v0)))))
         (coe (du56 (coe (MAlonzo.Code.Relation.Binary.d402 (coe v0))))))
name300
  = "Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-isTotalOrder-≡"
d300 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T876 ->
  MAlonzo.Code.Relation.Binary.T876
d300 v0 v1 v2 v3 v4 = du300 v4
du300 ::
  MAlonzo.Code.Relation.Binary.T876 ->
  MAlonzo.Code.Relation.Binary.T876
du300 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C5461
         (coe (du212 (coe (MAlonzo.Code.Relation.Binary.d894 (coe v0)))))
         (coe (du72 (coe (MAlonzo.Code.Relation.Binary.d896 (coe v0))))))
name342
  = "Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-isDecTotalOrder-≡"
d342 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T1010 ->
  MAlonzo.Code.Relation.Binary.T1010
d342 v0 v1 v2 v3 v4 = du342 v4
du342 ::
  MAlonzo.Code.Relation.Binary.T1010 ->
  MAlonzo.Code.Relation.Binary.T1010
du342 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C6205
         (coe (du300 (coe (MAlonzo.Code.Relation.Binary.d1030 (coe v0)))))
         (coe
            (MAlonzo.Code.Data.Maybe.Properties.du24
               (coe (MAlonzo.Code.Relation.Binary.d1032 (coe v0)))))
         (coe (du56 (coe (MAlonzo.Code.Relation.Binary.d1034 (coe v0))))))
name406
  = "Relation.Binary.Construct.Add.Supremum.NonStrict._._._≈∙_"
d406 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name436
  = "Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-isPreorder"
d436 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.T16
d436 v0 v1 v2 v3 v4 v5 v6 = du436 v6
du436 ::
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.T16
du436 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C17
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du108
               (coe (MAlonzo.Code.Relation.Binary.d36 (coe v0)))))
         (coe (du160 (coe (MAlonzo.Code.Relation.Binary.d38 (coe v0)))))
         (coe (du40 (coe (MAlonzo.Code.Relation.Binary.d40 (coe v0))))))
name470
  = "Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-isPartialOrder"
d470 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T256 ->
  MAlonzo.Code.Relation.Binary.T256
d470 v0 v1 v2 v3 v4 v5 v6 = du470 v6
du470 ::
  MAlonzo.Code.Relation.Binary.T256 ->
  MAlonzo.Code.Relation.Binary.T256
du470 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C1639
         (coe (du436 (coe (MAlonzo.Code.Relation.Binary.d274 (coe v0)))))
         (coe (du168 (coe (MAlonzo.Code.Relation.Binary.d276 (coe v0))))))
name508
  = "Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-isDecPartialOrder"
d508 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T378 ->
  MAlonzo.Code.Relation.Binary.T378
d508 v0 v1 v2 v3 v4 v5 v6 = du508 v6
du508 ::
  MAlonzo.Code.Relation.Binary.T378 ->
  MAlonzo.Code.Relation.Binary.T378
du508 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C2295
         (coe (du470 (coe (MAlonzo.Code.Relation.Binary.d398 (coe v0)))))
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du66
               (coe (MAlonzo.Code.Relation.Binary.d400 (coe v0)))))
         (coe (du56 (coe (MAlonzo.Code.Relation.Binary.d402 (coe v0))))))
name558
  = "Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-isTotalOrder"
d558 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T876 ->
  MAlonzo.Code.Relation.Binary.T876
d558 v0 v1 v2 v3 v4 v5 v6 = du558 v6
du558 ::
  MAlonzo.Code.Relation.Binary.T876 ->
  MAlonzo.Code.Relation.Binary.T876
du558 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C5461
         (coe (du470 (coe (MAlonzo.Code.Relation.Binary.d894 (coe v0)))))
         (coe (du72 (coe (MAlonzo.Code.Relation.Binary.d896 (coe v0))))))
name600
  = "Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-isDecTotalOrder"
d600 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T1010 ->
  MAlonzo.Code.Relation.Binary.T1010
d600 v0 v1 v2 v3 v4 v5 v6 = du600 v6
du600 ::
  MAlonzo.Code.Relation.Binary.T1010 ->
  MAlonzo.Code.Relation.Binary.T1010
du600 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C6205
         (coe (du558 (coe (MAlonzo.Code.Relation.Binary.d1030 (coe v0)))))
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du66
               (coe (MAlonzo.Code.Relation.Binary.d1032 (coe v0)))))
         (coe (du56 (coe (MAlonzo.Code.Relation.Binary.d1034 (coe v0))))))
name3755
  = "Relation.Binary.Construct.Add.Supremum.NonStrict..absurdlambda"
d3755 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d3755 = erased
