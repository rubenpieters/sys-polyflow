{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Nullary
import qualified MAlonzo.Code.Relation.Nullary.Decidable

name20 = "Relation.Binary.Construct.Add.Point.Equality._≈∙_"
d20 a0 a1 a2 a3 a4 a5 = ()
data T20 = C22 | C28 AgdaAny
name34
  = "Relation.Binary.Construct.Add.Point.Equality.[≈]-injective"
d34 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> T20 -> AgdaAny
d34 v0 v1 v2 v3 v4 v5 v6 = du34 v6
du34 :: T20 -> AgdaAny
du34 v0
  = case coe v0 of
      C28 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name38 = "Relation.Binary.Construct.Add.Point.Equality.≈∙-refl"
d38 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Data.Maybe.Base.T22 -> T20
d38 v0 v1 v2 v3 v4 v5 = du38 v4 v5
du38 ::
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Data.Maybe.Base.T22 -> T20
du38 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Maybe.Base.C28 v2
        -> coe (\ v3 v4 v5 -> C28 v5) erased erased (coe v0 v2)
      MAlonzo.Code.Data.Maybe.Base.C30 -> coe C22
      _ -> MAlonzo.RTE.mazUnreachableError
name46 = "Relation.Binary.Construct.Add.Point.Equality.≈∙-sym"
d46 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> T20 -> T20
d46 v0 v1 v2 v3 v4 v5 v6 v7 = du46 v4 v5 v6 v7
du46 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> T20 -> T20
du46 v0 v1 v2 v3
  = case coe v3 of
      C22 -> coe v3
      C28 v6
        -> case coe v1 of
             MAlonzo.Code.Data.Maybe.Base.C28 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Maybe.Base.C28 v8
                      -> coe (\ v9 v10 v11 -> C28 v11) erased erased (coe v0 v7 v8 v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name54 = "Relation.Binary.Construct.Add.Point.Equality.≈∙-trans"
d54 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> T20 -> T20 -> T20
d54 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du54 v4 v5 v6 v7 v8 v9
du54 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> T20 -> T20 -> T20
du54 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C22 -> coe v5
      C28 v8
        -> case coe v5 of
             C28 v11
               -> case coe v1 of
                    MAlonzo.Code.Data.Maybe.Base.C28 v12
                      -> case coe v2 of
                           MAlonzo.Code.Data.Maybe.Base.C28 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Data.Maybe.Base.C28 v14
                                    -> coe
                                         (\ v15 v16 v17 -> C28 v17) erased erased
                                         (coe v0 v12 v13 v14 v8 v11)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name66 = "Relation.Binary.Construct.Add.Point.Equality.≈∙-dec"
d66 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
d66 v0 v1 v2 v3 v4 v5 v6 = du66 v4 v5 v6
du66 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
du66 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Maybe.Base.C28 v3
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.du24
                    (coe (\ v5 v6 v7 -> C28 v7) erased erased) du34 (coe v0 v3 v4)
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe (\ v4 -> MAlonzo.Code.Relation.Nullary.C26) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Maybe.Base.C30
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v3
               -> coe (\ v4 -> MAlonzo.Code.Relation.Nullary.C26) erased
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe (MAlonzo.Code.Relation.Nullary.C22 (coe C22))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name84
  = "Relation.Binary.Construct.Add.Point.Equality.≈∙-irrelevant"
d84 ::
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
d84 = erased
name96
  = "Relation.Binary.Construct.Add.Point.Equality.≈∙-substitutive"
d96 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Data.Maybe.Base.T22 -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> T20 -> AgdaAny -> AgdaAny
d96 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du96 v5 v6 v7 v8 v9
du96 ::
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Data.Maybe.Base.T22 -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> T20 -> AgdaAny -> AgdaAny
du96 v0 v1 v2 v3 v4
  = case coe v4 of
      C22 -> coe (\ v5 -> v5)
      C28 v7
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Maybe.Base.C28 v9
                      -> coe
                           v0 (\ v10 -> coe v1 (MAlonzo.Code.Data.Maybe.Base.C28 (coe v10)))
                           v8 v9 v7
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name108
  = "Relation.Binary.Construct.Add.Point.Equality.≈∙-isEquivalence"
d108 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Core.T402 ->
  MAlonzo.Code.Relation.Binary.Core.T402
d108 v0 v1 v2 v3 v4 = du108 v4
du108 ::
  MAlonzo.Code.Relation.Binary.Core.T402 ->
  MAlonzo.Code.Relation.Binary.Core.T402
du108 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.C5081
         (coe
            (du38 (coe (MAlonzo.Code.Relation.Binary.Core.d414 (coe v0)))))
         (coe
            (du46 (coe (MAlonzo.Code.Relation.Binary.Core.d416 (coe v0)))))
         (coe
            (du54 (coe (MAlonzo.Code.Relation.Binary.Core.d418 (coe v0))))))
name126
  = "Relation.Binary.Construct.Add.Point.Equality.≈∙-isDecEquivalence"
d126 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T174 ->
  MAlonzo.Code.Relation.Binary.T174
d126 v0 v1 v2 v3 v4 = du126 v4
du126 ::
  MAlonzo.Code.Relation.Binary.T174 ->
  MAlonzo.Code.Relation.Binary.T174
du126 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C1313
         (coe (du108 (coe (MAlonzo.Code.Relation.Binary.d188 (coe v0)))))
         (coe (du66 (coe (MAlonzo.Code.Relation.Binary.d190 (coe v0))))))
name4523
  = "Relation.Binary.Construct.Add.Point.Equality..absurdlambda"
d4523 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d4523 = erased
name4841
  = "Relation.Binary.Construct.Add.Point.Equality..absurdlambda"
d4841 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d4841 = erased
