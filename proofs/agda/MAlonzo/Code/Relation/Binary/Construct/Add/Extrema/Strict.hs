{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Nullary

name22 = "Relation.Binary.Construct.Add.Extrema.Strict.Inf._<₋_"
d22 a0 a1 a2 a3 a4 a5 = ()
name82 = "Relation.Binary.Construct.Add.Extrema.Strict.Sup._<⁺_"
d82 a0 a1 a2 a3 a4 a5 = ()
name158
  = "Relation.Binary.Construct.Add.Extrema.Strict.[<]-injective"
d158 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  AgdaAny
d158 v0 v1 v2 v3 v4 v5 v6 = du158 v6
du158 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  AgdaAny
du158 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du36
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du36
               (coe v0))))
name160 = "Relation.Binary.Construct.Add.Extrema.Strict.<±-asym"
d160 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Data.Empty.T4
d160 = erased
name162 = "Relation.Binary.Construct.Add.Extrema.Strict.<±-trans"
d162 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
d162 v0 v1 v2 v3 v4 = du162 v4
du162 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
du162 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du48
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du48
               (coe v0))))
name164 = "Relation.Binary.Construct.Add.Extrema.Strict.<±-dec"
d164 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
d164 v0 v1 v2 v3 v4 = du164 v4
du164 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
du164 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du62
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du62
               (coe v0))))
name166
  = "Relation.Binary.Construct.Add.Extrema.Strict.<±-irrelevant"
d166 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d166 = erased
name178 = "Relation.Binary.Construct.Add.Extrema.Strict._._._≤⁺_"
d178 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name232
  = "Relation.Binary.Construct.Add.Extrema.Strict._.<±-transʳ"
d232 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
d232 v0 v1 v2 v3 v4 v5 v6 = du232 v6
du232 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
du232 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du154
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du154
               (coe v0))))
name234
  = "Relation.Binary.Construct.Add.Extrema.Strict._.<±-transˡ"
d234 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
d234 v0 v1 v2 v3 v4 v5 v6 = du234 v6
du234 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
du234 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du168
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du172
               (coe v0))))
name236 = "Relation.Binary.Construct.Add.Extrema.Strict.<±-cmp-≡"
d236 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Core.T198
d236 v0 v1 v2 v3 v4 = du236 v4
du236 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Core.T198
du236 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du184
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du186
               (coe v0))))
name238
  = "Relation.Binary.Construct.Add.Extrema.Strict.<±-irrefl-≡"
d238 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T12 ->
   AgdaAny -> MAlonzo.Code.Data.Empty.T4) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Data.Empty.T4
d238 = erased
name240 = "Relation.Binary.Construct.Add.Extrema.Strict.<±-respˡ-≡"
d240 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
d240 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du240 v8
du240 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
du240 v0 = coe v0
name242 = "Relation.Binary.Construct.Add.Extrema.Strict.<±-respʳ-≡"
d242 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
d242 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du242 v8
du242 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
du242 v0 = coe v0
name244 = "Relation.Binary.Construct.Add.Extrema.Strict.<±-resp-≡"
d244 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d244 v0 v1 v2 v3 = du244
du244 :: MAlonzo.Code.Agda.Builtin.Sigma.T14
du244
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du254
name256 = "Relation.Binary.Construct.Add.Extrema.Strict._._._≈∙_"
d256 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name282 = "Relation.Binary.Construct.Add.Extrema.Strict._.<±-cmp"
d282 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Core.T198
d282 v0 v1 v2 v3 v4 v5 v6 = du282 v6
du282 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Core.T198
du282 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du296
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du298
               (coe v0))))
name284
  = "Relation.Binary.Construct.Add.Extrema.Strict._.<±-irrefl"
d284 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Data.Empty.T4
d284 = erased
name286
  = "Relation.Binary.Construct.Add.Extrema.Strict._.<±-respˡ-≈±"
d286 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
d286 v0 v1 v2 v3 v4 v5 v6 = du286 v6
du286 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
du286 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du362
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du364
               (coe v0))))
name288
  = "Relation.Binary.Construct.Add.Extrema.Strict._.<±-respʳ-≈±"
d288 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
d288 v0 v1 v2 v3 v4 v5 v6 = du288 v6
du288 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
du288 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du380
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du376
               (coe v0))))
name290
  = "Relation.Binary.Construct.Add.Extrema.Strict._.<±-resp-≈±"
d290 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d290 v0 v1 v2 v3 v4 v5 v6 = du290 v6
du290 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du290 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du392
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du394 v0)
name292
  = "Relation.Binary.Construct.Add.Extrema.Strict.<±-isStrictPartialOrder-≡"
d292 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T570 ->
  MAlonzo.Code.Relation.Binary.T570
d292 v0 v1 v2 v3 v4 = du292 v4
du292 ::
  MAlonzo.Code.Relation.Binary.T570 ->
  MAlonzo.Code.Relation.Binary.T570
du292 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du394
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du396
               (coe v0))))
name294
  = "Relation.Binary.Construct.Add.Extrema.Strict.<±-isDecStrictPartialOrder-≡"
d294 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T692 ->
  MAlonzo.Code.Relation.Binary.T692
d294 v0 v1 v2 v3 v4 = du294 v4
du294 ::
  MAlonzo.Code.Relation.Binary.T692 ->
  MAlonzo.Code.Relation.Binary.T692
du294 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du430
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du432
               (coe v0))))
name296
  = "Relation.Binary.Construct.Add.Extrema.Strict.<±-isStrictTotalOrder-≡"
d296 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T1202 ->
  MAlonzo.Code.Relation.Binary.T1202
d296 v0 v1 v2 v3 v4 = du296 v4
du296 ::
  MAlonzo.Code.Relation.Binary.T1202 ->
  MAlonzo.Code.Relation.Binary.T1202
du296 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du478
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du480
               (coe v0))))
name308 = "Relation.Binary.Construct.Add.Extrema.Strict._._._≈∙_"
d308 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name334
  = "Relation.Binary.Construct.Add.Extrema.Strict._.<±-isStrictPartialOrder"
d334 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T570 ->
  MAlonzo.Code.Relation.Binary.T570
d334 v0 v1 v2 v3 v4 v5 v6 = du334 v6
du334 ::
  MAlonzo.Code.Relation.Binary.T570 ->
  MAlonzo.Code.Relation.Binary.T570
du334 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du566
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du568
               (coe v0))))
name336
  = "Relation.Binary.Construct.Add.Extrema.Strict._.<±-isDecStrictPartialOrder"
d336 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T692 ->
  MAlonzo.Code.Relation.Binary.T692
d336 v0 v1 v2 v3 v4 v5 v6 = du336 v6
du336 ::
  MAlonzo.Code.Relation.Binary.T692 ->
  MAlonzo.Code.Relation.Binary.T692
du336 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du602
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du604
               (coe v0))))
name338
  = "Relation.Binary.Construct.Add.Extrema.Strict._.<±-isStrictTotalOrder"
d338 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T1202 ->
  MAlonzo.Code.Relation.Binary.T1202
d338 v0 v1 v2 v3 v4 v5 v6 = du338 v6
du338 ::
  MAlonzo.Code.Relation.Binary.T1202 ->
  MAlonzo.Code.Relation.Binary.T1202
du338 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du650
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du652
               (coe v0))))
