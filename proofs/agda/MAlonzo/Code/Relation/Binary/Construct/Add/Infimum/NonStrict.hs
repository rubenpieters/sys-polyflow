{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict where

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

name20 = "Relation.Binary.Construct.Add.Infimum.NonStrict._≤₋_"
d20 a0 a1 a2 a3 a4 a5 = ()
data T20 = C24 | C30 AgdaAny
name36
  = "Relation.Binary.Construct.Add.Infimum.NonStrict.[≤]-injective"
d36 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> T20 -> AgdaAny
d36 v0 v1 v2 v3 v4 v5 v6 = du36 v6
du36 :: T20 -> AgdaAny
du36 v0
  = case coe v0 of
      C30 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name40 = "Relation.Binary.Construct.Add.Infimum.NonStrict.≤₋-trans"
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
  = case coe v4 of
      C24 -> coe (\ v7 -> C24) erased
      C30 v8
        -> case coe v5 of
             C30 v11
               -> case coe v1 of
                    MAlonzo.Code.Data.Maybe.Base.C28 v12
                      -> case coe v2 of
                           MAlonzo.Code.Data.Maybe.Base.C28 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Data.Maybe.Base.C28 v14
                                    -> coe
                                         (\ v15 v16 v17 -> C30 v17) erased erased
                                         (coe v0 v12 v13 v14 v8 v11)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name54
  = "Relation.Binary.Construct.Add.Infimum.NonStrict.≤₋-minimum"
d54 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> T20
d54 v0 v1 v2 v3 = du54
du54 :: MAlonzo.Code.Data.Maybe.Base.T22 -> T20
du54 = coe (\ v0 -> C24)
name56 = "Relation.Binary.Construct.Add.Infimum.NonStrict.≤₋-dec"
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
  = case coe v1 of
      MAlonzo.Code.Data.Maybe.Base.C28 v3
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.du24
                    (coe (\ v5 v6 v7 -> C30 v7) erased erased) du36 (coe v0 v3 v4)
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe (\ v4 -> MAlonzo.Code.Relation.Nullary.C26) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Maybe.Base.C30
        -> coe
             (MAlonzo.Code.Relation.Nullary.C22 (coe (\ v3 -> C24) erased))
      _ -> MAlonzo.RTE.mazUnreachableError
name72 = "Relation.Binary.Construct.Add.Infimum.NonStrict.≤₋-total"
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
  = case coe v1 of
      MAlonzo.Code.Data.Maybe.Base.C28 v3
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.du74
                    (coe (\ v5 v6 v7 -> C30 v7) erased erased)
                    (coe (\ v5 v6 v7 -> C30 v7) erased erased) (coe v0 v3 v4)
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe (MAlonzo.Code.Data.Sum.Base.C42 (coe (\ v4 -> C24) erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Maybe.Base.C30
        -> coe (MAlonzo.Code.Data.Sum.Base.C38 (coe (\ v3 -> C24) erased))
      _ -> MAlonzo.RTE.mazUnreachableError
name88
  = "Relation.Binary.Construct.Add.Infimum.NonStrict.≤₋-irrelevant"
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
  = "Relation.Binary.Construct.Add.Infimum.NonStrict.≤₋-reflexive-≡"
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
        -> coe (\ v3 v4 v5 -> C30 v5) erased erased (coe v0 v2 v2 erased)
      MAlonzo.Code.Data.Maybe.Base.C30 -> coe (\ v2 -> C24) erased
      _ -> MAlonzo.RTE.mazUnreachableError
name108
  = "Relation.Binary.Construct.Add.Infimum.NonStrict.≤₋-antisym-≡"
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
name128
  = "Relation.Binary.Construct.Add.Infimum.NonStrict._._._≈∙_"
d128 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name158
  = "Relation.Binary.Construct.Add.Infimum.NonStrict._.≤₋-reflexive"
d158 ::
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
d158 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du158 v6 v7 v8 v9
du158 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  T20
du158 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C22
        -> coe (\ v4 -> C24) erased
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C28 v6
        -> case coe v1 of
             MAlonzo.Code.Data.Maybe.Base.C28 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Maybe.Base.C28 v8
                      -> coe (\ v9 v10 v11 -> C30 v11) erased erased (coe v0 v7 v8 v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name166
  = "Relation.Binary.Construct.Add.Infimum.NonStrict._.≤₋-antisym"
d166 ::
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
d166 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du166 v6 v7 v8 v9 v10
du166 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  T20 ->
  T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
du166 v0 v1 v2 v3 v4
  = case coe v3 of
      C24
        -> case coe v1 of
             MAlonzo.Code.Data.Maybe.Base.C30
               -> case coe v4 of
                    C24
                      -> coe
                           MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C22
                    _ -> erased
             _ -> erased
      C30 v7
        -> case coe v4 of
             C30 v10
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
      _ -> MAlonzo.RTE.mazUnreachableError
name176
  = "Relation.Binary.Construct.Add.Infimum.NonStrict.≤₋-isPreorder-≡"
d176 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.T16
d176 v0 v1 v2 v3 v4 = du176 v4
du176 ::
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.T16
du176 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C17
         (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du70)
         (coe
            (\ v1 v2 v3 ->
               du100 (coe (MAlonzo.Code.Relation.Binary.d38 (coe v0))) v1))
         (coe (du40 (coe (MAlonzo.Code.Relation.Binary.d40 (coe v0))))))
name210
  = "Relation.Binary.Construct.Add.Infimum.NonStrict.≤₋-isPartialOrder-≡"
d210 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T256 ->
  MAlonzo.Code.Relation.Binary.T256
d210 v0 v1 v2 v3 v4 = du210 v4
du210 ::
  MAlonzo.Code.Relation.Binary.T256 ->
  MAlonzo.Code.Relation.Binary.T256
du210 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C1639
         (coe (du176 (coe (MAlonzo.Code.Relation.Binary.d274 (coe v0)))))
         erased)
name248
  = "Relation.Binary.Construct.Add.Infimum.NonStrict.≤₋-isDecPartialOrder-≡"
d248 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T378 ->
  MAlonzo.Code.Relation.Binary.T378
d248 v0 v1 v2 v3 v4 = du248 v4
du248 ::
  MAlonzo.Code.Relation.Binary.T378 ->
  MAlonzo.Code.Relation.Binary.T378
du248 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C2295
         (coe (du210 (coe (MAlonzo.Code.Relation.Binary.d398 (coe v0)))))
         (coe
            (MAlonzo.Code.Data.Maybe.Properties.du24
               (coe (MAlonzo.Code.Relation.Binary.d400 (coe v0)))))
         (coe (du56 (coe (MAlonzo.Code.Relation.Binary.d402 (coe v0))))))
name298
  = "Relation.Binary.Construct.Add.Infimum.NonStrict.≤₋-isTotalOrder-≡"
d298 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T876 ->
  MAlonzo.Code.Relation.Binary.T876
d298 v0 v1 v2 v3 v4 = du298 v4
du298 ::
  MAlonzo.Code.Relation.Binary.T876 ->
  MAlonzo.Code.Relation.Binary.T876
du298 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C5461
         (coe (du210 (coe (MAlonzo.Code.Relation.Binary.d894 (coe v0)))))
         (coe (du72 (coe (MAlonzo.Code.Relation.Binary.d896 (coe v0))))))
name340
  = "Relation.Binary.Construct.Add.Infimum.NonStrict.≤₋-isDecTotalOrder-≡"
d340 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T1010 ->
  MAlonzo.Code.Relation.Binary.T1010
d340 v0 v1 v2 v3 v4 = du340 v4
du340 ::
  MAlonzo.Code.Relation.Binary.T1010 ->
  MAlonzo.Code.Relation.Binary.T1010
du340 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C6205
         (coe (du298 (coe (MAlonzo.Code.Relation.Binary.d1030 (coe v0)))))
         (coe
            (MAlonzo.Code.Data.Maybe.Properties.du24
               (coe (MAlonzo.Code.Relation.Binary.d1032 (coe v0)))))
         (coe (du56 (coe (MAlonzo.Code.Relation.Binary.d1034 (coe v0))))))
name404
  = "Relation.Binary.Construct.Add.Infimum.NonStrict._._._≈∙_"
d404 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name434
  = "Relation.Binary.Construct.Add.Infimum.NonStrict._.≤₋-isPreorder"
d434 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.T16
d434 v0 v1 v2 v3 v4 v5 v6 = du434 v6
du434 ::
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.T16
du434 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C17
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du108
               (coe (MAlonzo.Code.Relation.Binary.d36 (coe v0)))))
         (coe (du158 (coe (MAlonzo.Code.Relation.Binary.d38 (coe v0)))))
         (coe (du40 (coe (MAlonzo.Code.Relation.Binary.d40 (coe v0))))))
name468
  = "Relation.Binary.Construct.Add.Infimum.NonStrict._.≤₋-isPartialOrder"
d468 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T256 ->
  MAlonzo.Code.Relation.Binary.T256
d468 v0 v1 v2 v3 v4 v5 v6 = du468 v6
du468 ::
  MAlonzo.Code.Relation.Binary.T256 ->
  MAlonzo.Code.Relation.Binary.T256
du468 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C1639
         (coe (du434 (coe (MAlonzo.Code.Relation.Binary.d274 (coe v0)))))
         (coe (du166 (coe (MAlonzo.Code.Relation.Binary.d276 (coe v0))))))
name506
  = "Relation.Binary.Construct.Add.Infimum.NonStrict._.≤₋-isDecPartialOrder"
d506 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T378 ->
  MAlonzo.Code.Relation.Binary.T378
d506 v0 v1 v2 v3 v4 v5 v6 = du506 v6
du506 ::
  MAlonzo.Code.Relation.Binary.T378 ->
  MAlonzo.Code.Relation.Binary.T378
du506 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C2295
         (coe (du468 (coe (MAlonzo.Code.Relation.Binary.d398 (coe v0)))))
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du66
               (coe (MAlonzo.Code.Relation.Binary.d400 (coe v0)))))
         (coe (du56 (coe (MAlonzo.Code.Relation.Binary.d402 (coe v0))))))
name556
  = "Relation.Binary.Construct.Add.Infimum.NonStrict._.≤₋-isTotalOrder"
d556 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T876 ->
  MAlonzo.Code.Relation.Binary.T876
d556 v0 v1 v2 v3 v4 v5 v6 = du556 v6
du556 ::
  MAlonzo.Code.Relation.Binary.T876 ->
  MAlonzo.Code.Relation.Binary.T876
du556 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C5461
         (coe (du468 (coe (MAlonzo.Code.Relation.Binary.d894 (coe v0)))))
         (coe (du72 (coe (MAlonzo.Code.Relation.Binary.d896 (coe v0))))))
name598
  = "Relation.Binary.Construct.Add.Infimum.NonStrict._.≤₋-isDecTotalOrder"
d598 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T1010 ->
  MAlonzo.Code.Relation.Binary.T1010
d598 v0 v1 v2 v3 v4 v5 v6 = du598 v6
du598 ::
  MAlonzo.Code.Relation.Binary.T1010 ->
  MAlonzo.Code.Relation.Binary.T1010
du598 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C6205
         (coe (du556 (coe (MAlonzo.Code.Relation.Binary.d1030 (coe v0)))))
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du66
               (coe (MAlonzo.Code.Relation.Binary.d1032 (coe v0)))))
         (coe (du56 (coe (MAlonzo.Code.Relation.Binary.d1034 (coe v0))))))
name3371
  = "Relation.Binary.Construct.Add.Infimum.NonStrict..absurdlambda"
d3371 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d3371 = erased
