{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.NonStrict where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict
import qualified MAlonzo.Code.Relation.Nullary

name22 = "Relation.Binary.Construct.Add.Extrema.NonStrict.Inf._≤₋_"
d22 a0 a1 a2 a3 a4 a5 = ()
name76 = "Relation.Binary.Construct.Add.Extrema.NonStrict.Sup._≤⁺_"
d76 a0 a1 a2 a3 a4 a5 = ()
name148 = "Relation.Binary.Construct.Add.Extrema.NonStrict.⊥±≤_"
d148 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
d148 v0 v1 v2 v3 v4 = du148 v4
du148 ::
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
du148 v0
  = case coe v0 of
      MAlonzo.Code.Data.Maybe.Base.C28 v1
        -> coe
             (seq
                (coe v1)
                (coe
                   (\ v2 v3 v4 ->
                      MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C26
                        v4)
                   erased erased
                   (coe
                      (\ v2 ->
                         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.C24)
                      erased)))
      MAlonzo.Code.Data.Maybe.Base.C30
        -> coe
             (\ v1 ->
                MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C30)
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
name154 = "Relation.Binary.Construct.Add.Extrema.NonStrict._≤⊤±"
d154 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
d154 v0 v1 v2 v3 v4 = du154 v4
du154 ::
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
du154 v0
  = case coe v0 of
      MAlonzo.Code.Data.Maybe.Base.C28 v1
        -> coe
             (seq
                (coe v1)
                (coe
                   (\ v2 ->
                      MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C30)
                   erased))
      MAlonzo.Code.Data.Maybe.Base.C30
        -> coe
             (\ v1 ->
                MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C30)
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
name162
  = "Relation.Binary.Construct.Add.Extrema.NonStrict.[≤]-injective"
d162 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  AgdaAny
d162 v0 v1 v2 v3 v4 v5 v6 = du162 v6
du162 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  AgdaAny
du162 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du36
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du36
               (coe v0))))
name164
  = "Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-trans"
d164 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
d164 v0 v1 v2 v3 v4 = du164 v4
du164 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
du164 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du40
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du40
               (coe v0))))
name166
  = "Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-minimum"
d166 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
d166 v0 v1 v2 v3 = du166
du166 ::
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
du166 = coe du148
name168
  = "Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-maximum"
d168 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
d168 v0 v1 v2 v3 = du168
du168 ::
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
du168 = coe du154
name170 = "Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-dec"
d170 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
d170 v0 v1 v2 v3 v4 = du170 v4
du170 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
du170 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du56
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du56
               (coe v0))))
name172
  = "Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-total"
d172 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T30) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> MAlonzo.Code.Data.Sum.Base.T30
d172 v0 v1 v2 v3 v4 = du172 v4
du172 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T30) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> MAlonzo.Code.Data.Sum.Base.T30
du172 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du72
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du72
               (coe v0))))
name174
  = "Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-irrelevant"
d174 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d174 = erased
name176
  = "Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-reflexive-≡"
d176 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
d176 v0 v1 v2 v3 v4 = du176 v4
du176 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
du176 v0
  = coe
      (\ v1 v2 v3 ->
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du100
           (coe
              (\ v4 v5 v6 ->
                 MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du100
                   (coe v0) v4))
           v1)
name178
  = "Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-antisym-≡"
d178 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d178 = erased
name190
  = "Relation.Binary.Construct.Add.Extrema.NonStrict._._._≈∙_"
d190 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name216
  = "Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-reflexive"
d216 ::
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
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
d216 v0 v1 v2 v3 v4 v5 v6 = du216 v6
du216 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20
du216 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du160
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du158
               (coe v0))))
name218
  = "Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-antisym"
d218 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
d218 v0 v1 v2 v3 v4 v5 v6 = du218 v6
du218 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
du218 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du168
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du166
               (coe v0))))
name220
  = "Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-isPreorder-≡"
d220 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.T16
d220 v0 v1 v2 v3 v4 = du220 v4
du220 ::
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.T16
du220 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du178
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du176
               (coe v0))))
name222
  = "Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-isPartialOrder-≡"
d222 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T256 ->
  MAlonzo.Code.Relation.Binary.T256
d222 v0 v1 v2 v3 v4 = du222 v4
du222 ::
  MAlonzo.Code.Relation.Binary.T256 ->
  MAlonzo.Code.Relation.Binary.T256
du222 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du212
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du210
               (coe v0))))
name224
  = "Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-isDecPartialOrder-≡"
d224 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T378 ->
  MAlonzo.Code.Relation.Binary.T378
d224 v0 v1 v2 v3 v4 = du224 v4
du224 ::
  MAlonzo.Code.Relation.Binary.T378 ->
  MAlonzo.Code.Relation.Binary.T378
du224 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du250
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du248
               (coe v0))))
name226
  = "Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-isTotalOrder-≡"
d226 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T876 ->
  MAlonzo.Code.Relation.Binary.T876
d226 v0 v1 v2 v3 v4 = du226 v4
du226 ::
  MAlonzo.Code.Relation.Binary.T876 ->
  MAlonzo.Code.Relation.Binary.T876
du226 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du300
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du298
               (coe v0))))
name228
  = "Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-isDecTotalOrder-≡"
d228 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T1010 ->
  MAlonzo.Code.Relation.Binary.T1010
d228 v0 v1 v2 v3 v4 = du228 v4
du228 ::
  MAlonzo.Code.Relation.Binary.T1010 ->
  MAlonzo.Code.Relation.Binary.T1010
du228 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du342
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du340
               (coe v0))))
name240
  = "Relation.Binary.Construct.Add.Extrema.NonStrict._._._≈∙_"
d240 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name266
  = "Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-isPreorder"
d266 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.T16
d266 v0 v1 v2 v3 v4 v5 v6 = du266 v6
du266 ::
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.T16
du266 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du436
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du434
               (coe v0))))
name268
  = "Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-isPartialOrder"
d268 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T256 ->
  MAlonzo.Code.Relation.Binary.T256
d268 v0 v1 v2 v3 v4 v5 v6 = du268 v6
du268 ::
  MAlonzo.Code.Relation.Binary.T256 ->
  MAlonzo.Code.Relation.Binary.T256
du268 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du470
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du468
               (coe v0))))
name270
  = "Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-isDecPartialOrder"
d270 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T378 ->
  MAlonzo.Code.Relation.Binary.T378
d270 v0 v1 v2 v3 v4 v5 v6 = du270 v6
du270 ::
  MAlonzo.Code.Relation.Binary.T378 ->
  MAlonzo.Code.Relation.Binary.T378
du270 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du508
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du506
               (coe v0))))
name272
  = "Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-isTotalOrder"
d272 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T876 ->
  MAlonzo.Code.Relation.Binary.T876
d272 v0 v1 v2 v3 v4 v5 v6 = du272 v6
du272 ::
  MAlonzo.Code.Relation.Binary.T876 ->
  MAlonzo.Code.Relation.Binary.T876
du272 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du558
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du556
               (coe v0))))
name274
  = "Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-isDecTotalOrder"
d274 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T1010 ->
  MAlonzo.Code.Relation.Binary.T1010
d274 v0 v1 v2 v3 v4 v5 v6 = du274 v6
du274 ::
  MAlonzo.Code.Relation.Binary.T1010 ->
  MAlonzo.Code.Relation.Binary.T1010
du274 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du600
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du598
               (coe v0))))
