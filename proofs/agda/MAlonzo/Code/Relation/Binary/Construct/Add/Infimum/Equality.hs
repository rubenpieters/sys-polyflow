{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Equality where

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

name22 = "Relation.Binary.Construct.Add.Infimum.Equality._._≈∙_"
d22 a0 a1 a2 a3 a4 a5 = ()
name26
  = "Relation.Binary.Construct.Add.Infimum.Equality._.[≈]-injective"
d26 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  AgdaAny
d26 v0 v1 v2 v3 = du26
du26 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  AgdaAny
du26
  = coe
      (\ v0 v1 v2 ->
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du34 v2)
name28 = "Relation.Binary.Construct.Add.Infimum.Equality._.≈∙-dec"
d28 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
d28 v0 v1 v2 v3 = du28
du28 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
du28
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du66
name30
  = "Relation.Binary.Construct.Add.Infimum.Equality._.≈∙-irrelevant"
d30 ::
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
d30 = erased
name32
  = "Relation.Binary.Construct.Add.Infimum.Equality._.≈∙-isDecEquivalence"
d32 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T174 ->
  MAlonzo.Code.Relation.Binary.T174
d32 v0 v1 v2 v3 = du32
du32 ::
  MAlonzo.Code.Relation.Binary.T174 ->
  MAlonzo.Code.Relation.Binary.T174
du32
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du126
name34
  = "Relation.Binary.Construct.Add.Infimum.Equality._.≈∙-isEquivalence"
d34 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Core.T402 ->
  MAlonzo.Code.Relation.Binary.Core.T402
d34 v0 v1 v2 v3 = du34
du34 ::
  MAlonzo.Code.Relation.Binary.Core.T402 ->
  MAlonzo.Code.Relation.Binary.Core.T402
du34
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du108
name36 = "Relation.Binary.Construct.Add.Infimum.Equality._.≈∙-refl"
d36 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
d36 v0 v1 v2 v3 = du36
du36 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
du36
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du38
name38
  = "Relation.Binary.Construct.Add.Infimum.Equality._.≈∙-substitutive"
d38 ::
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
d38 v0 v1 v2 v3 = du38
du38 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Data.Maybe.Base.T22 -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  AgdaAny -> AgdaAny
du38
  = coe
      (\ v0 v1 v2 v3 v4 v5 ->
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du96
           v1 v2 v3 v4 v5)
name40 = "Relation.Binary.Construct.Add.Infimum.Equality._.≈∙-sym"
d40 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
d40 v0 v1 v2 v3 = du40
du40 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
du40
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du46
name42
  = "Relation.Binary.Construct.Add.Infimum.Equality._.≈∙-trans"
d42 ::
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
d42 v0 v1 v2 v3 = du42
du42 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20
du42
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du54
