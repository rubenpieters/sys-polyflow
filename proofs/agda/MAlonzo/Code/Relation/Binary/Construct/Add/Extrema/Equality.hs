{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Equality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Nullary

name22 = "Relation.Binary.Construct.Add.Extrema.Equality.Inf._≈∙_"
d22 a0 a1 a2 a3 a4 a5 = ()
name54 = "Relation.Binary.Construct.Add.Extrema.Equality.Sup._≈∙_"
d54 a0 a1 a2 a3 a4 a5 = ()
name96
  = "Relation.Binary.Construct.Add.Extrema.Equality.[≈]-injective"
d96 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  AgdaAny
d96 v0 v1 v2 v3 v4 v5 v6 = du96 v6
du96 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  AgdaAny
du96 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du34
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du34
               (coe v0))))
name98 = "Relation.Binary.Construct.Add.Extrema.Equality.≈±-refl"
d98 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
d98 v0 v1 v2 v3 v4 = du98 v4
du98 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
du98 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du38
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du38
               (coe v0))))
name100 = "Relation.Binary.Construct.Add.Extrema.Equality.≈±-sym"
d100 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
d100 v0 v1 v2 v3 v4 = du100 v4
du100 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
du100 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du46
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du46
               (coe v0))))
name102 = "Relation.Binary.Construct.Add.Extrema.Equality.≈±-trans"
d102 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
d102 v0 v1 v2 v3 v4 = du102 v4
du102 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
du102 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du54
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du54
               (coe v0))))
name104 = "Relation.Binary.Construct.Add.Extrema.Equality.≈±-dec"
d104 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
d104 v0 v1 v2 v3 v4 = du104 v4
du104 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
du104 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du66
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du66
               (coe v0))))
name106
  = "Relation.Binary.Construct.Add.Extrema.Equality.≈±-irrelevant"
d106 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d106 = erased
name110
  = "Relation.Binary.Construct.Add.Extrema.Equality.≈±-substitutive"
d110 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Data.Maybe.Base.T22 -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  AgdaAny -> AgdaAny
d110 v0 v1 v2 v3 v4 v5 = du110 v5
du110 ::
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Data.Maybe.Base.T22 -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  AgdaAny -> AgdaAny
du110 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du96
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du96
               (coe v0))))
name112
  = "Relation.Binary.Construct.Add.Extrema.Equality.≈±-isEquivalence"
d112 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Core.T402 ->
  MAlonzo.Code.Relation.Binary.Core.T402
d112 v0 v1 v2 v3 v4 = du112 v4
du112 ::
  MAlonzo.Code.Relation.Binary.Core.T402 ->
  MAlonzo.Code.Relation.Binary.Core.T402
du112 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du108
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du108
               (coe v0))))
name114
  = "Relation.Binary.Construct.Add.Extrema.Equality.≈±-isDecEquivalence"
d114 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T174 ->
  MAlonzo.Code.Relation.Binary.T174
d114 v0 v1 v2 v3 v4 = du114 v4
du114 ::
  MAlonzo.Code.Relation.Binary.T174 ->
  MAlonzo.Code.Relation.Binary.T174
du114 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du126
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du126
               (coe v0))))
