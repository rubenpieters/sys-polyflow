{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict where

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
import qualified MAlonzo.Code.Data.Maybe.Properties
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary
import qualified MAlonzo.Code.Relation.Nullary.Decidable

name20 = "Relation.Binary.Construct.Add.Supremum.Strict._<⁺_"
d20 a0 a1 a2 a3 a4 a5 = ()
data T20 = C26 AgdaAny | C30
name36
  = "Relation.Binary.Construct.Add.Supremum.Strict.[<]-injective"
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
name40 = "Relation.Binary.Construct.Add.Supremum.Strict.<⁺-asym"
d40 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  T20 -> T20 -> MAlonzo.Code.Data.Empty.T4
d40 = erased
name48 = "Relation.Binary.Construct.Add.Supremum.Strict.<⁺-trans"
d48 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> T20 -> T20 -> T20
d48 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du48 v4 v5 v6 v7 v8 v9
du48 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> T20 -> T20 -> T20
du48 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C26 v8
        -> case coe v5 of
             C26 v11
               -> case coe v1 of
                    MAlonzo.Code.Data.Maybe.Base.C28 v12
                      -> case coe v2 of
                           MAlonzo.Code.Data.Maybe.Base.C28 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Data.Maybe.Base.C28 v14
                                    -> coe
                                         (\ v15 v16 v17 -> C26 v17) erased erased
                                         (coe v0 v12 v13 v14 v8 v11)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C30 -> coe (\ v10 -> C30) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name62 = "Relation.Binary.Construct.Add.Supremum.Strict.<⁺-dec"
d62 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
d62 v0 v1 v2 v3 v4 v5 v6 = du62 v4 v5 v6
du62 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Nullary.T14
du62 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Maybe.Base.C28 v3
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.du24
                    (coe (\ v5 v6 v7 -> C26 v7) erased erased) du36 (coe v0 v3 v4)
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe
                    (MAlonzo.Code.Relation.Nullary.C22 (coe (\ v4 -> C30) erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Maybe.Base.C30
        -> coe
             (seq
                (coe v2) (coe (\ v3 -> MAlonzo.Code.Relation.Nullary.C26) erased))
      _ -> MAlonzo.RTE.mazUnreachableError
name80
  = "Relation.Binary.Construct.Add.Supremum.Strict.<⁺-irrelevant"
d80 ::
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
d80 = erased
name102 = "Relation.Binary.Construct.Add.Supremum.Strict._._._≤⁺_"
d102 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name154
  = "Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-transʳ"
d154 ::
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
  T20 -> T20
d154 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du154 v6 v7 v8 v9 v10 v11
du154 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  T20 -> T20
du154 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C26 v8
        -> case coe v5 of
             C26 v11
               -> case coe v1 of
                    MAlonzo.Code.Data.Maybe.Base.C28 v12
                      -> case coe v2 of
                           MAlonzo.Code.Data.Maybe.Base.C28 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Data.Maybe.Base.C28 v14
                                    -> coe
                                         (\ v15 v16 v17 -> C26 v17) erased erased
                                         (coe v0 v12 v13 v14 v8 v11)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C30 -> coe (\ v10 -> C30) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name168
  = "Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-transˡ"
d168 ::
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
  T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  T20
d168 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du168 v6 v7 v8 v9 v10 v11
du168 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T20 ->
  T20
du168 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C26 v8
        -> case coe v5 of
             MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C26 v11
               -> case coe v1 of
                    MAlonzo.Code.Data.Maybe.Base.C28 v12
                      -> case coe v2 of
                           MAlonzo.Code.Data.Maybe.Base.C28 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Data.Maybe.Base.C28 v14
                                    -> coe
                                         (\ v15 v16 v17 -> C26 v17) erased erased
                                         (coe v0 v12 v13 v14 v8 v11)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C30
               -> coe (\ v10 -> C30) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      C30 -> coe (seq (coe v5) (coe (\ v7 -> C30) erased))
      _ -> MAlonzo.RTE.mazUnreachableError
name184 = "Relation.Binary.Construct.Add.Supremum.Strict.<⁺-cmp-≡"
d184 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Core.T198
d184 v0 v1 v2 v3 v4 v5 v6 = du184 v4 v5 v6
du184 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Core.T198
du184 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Maybe.Base.C28 v3
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v4
               -> let v5 = coe v0 v3 v4 in
                  case coe v5 of
                    MAlonzo.Code.Relation.Binary.Core.C212 v6
                      -> coe
                           (\ v9 v10 v11 -> MAlonzo.Code.Relation.Binary.Core.C212 v9)
                           (coe (\ v9 v10 v11 -> C26 v11) erased erased v6) erased erased
                    MAlonzo.Code.Relation.Binary.Core.C220 v7
                      -> coe
                           (\ v9 v10 v11 -> MAlonzo.Code.Relation.Binary.Core.C220 v10) erased
                           erased erased
                    MAlonzo.Code.Relation.Binary.Core.C228 v8
                      -> coe
                           (\ v9 v10 v11 -> MAlonzo.Code.Relation.Binary.Core.C228 v11) erased
                           erased (coe (\ v9 v10 v11 -> C26 v11) erased erased v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe
                    (\ v4 v5 v6 -> MAlonzo.Code.Relation.Binary.Core.C212 v4)
                    (coe (\ v4 -> C30) erased) erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Maybe.Base.C30
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v3
               -> coe
                    (\ v4 v5 v6 -> MAlonzo.Code.Relation.Binary.Core.C228 v6) erased
                    erased (coe (\ v4 -> C30) erased)
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe
                    (\ v3 v4 v5 -> MAlonzo.Code.Relation.Binary.Core.C220 v4) erased
                    erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name240
  = "Relation.Binary.Construct.Add.Supremum.Strict.<⁺-irrefl-≡"
d240 ::
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
  T20 -> MAlonzo.Code.Data.Empty.T4
d240 = erased
name246
  = "Relation.Binary.Construct.Add.Supremum.Strict.<⁺-respˡ-≡"
d246 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 -> T20 -> T20
d246 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du246 v8
du246 :: T20 -> T20
du246 v0 = coe v0
name250
  = "Relation.Binary.Construct.Add.Supremum.Strict.<⁺-respʳ-≡"
d250 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 -> T20 -> T20
d250 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du250 v8
du250 :: T20 -> T20
du250 v0 = coe v0
name254 = "Relation.Binary.Construct.Add.Supremum.Strict.<⁺-resp-≡"
d254 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d254 v0 v1 v2 v3 = du254
du254 :: MAlonzo.Code.Agda.Builtin.Sigma.T14
du254
  = coe
      (MAlonzo.Code.Agda.Builtin.Sigma.C32
         (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4)))
name266 = "Relation.Binary.Construct.Add.Supremum.Strict._._._≈∙_"
d266 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name296 = "Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-cmp"
d296 ::
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
d296 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du296 v6 v7 v8
du296 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Core.T198
du296 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Maybe.Base.C28 v3
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v4
               -> let v5 = coe v0 v3 v4 in
                  case coe v5 of
                    MAlonzo.Code.Relation.Binary.Core.C212 v6
                      -> coe
                           (\ v9 v10 v11 -> MAlonzo.Code.Relation.Binary.Core.C212 v9)
                           (coe (\ v9 v10 v11 -> C26 v11) erased erased v6) erased erased
                    MAlonzo.Code.Relation.Binary.Core.C220 v7
                      -> coe
                           (\ v9 v10 v11 -> MAlonzo.Code.Relation.Binary.Core.C220 v10) erased
                           (coe
                              (\ v9 v10 v11 ->
                                 MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C28 v11)
                              erased erased v7)
                           erased
                    MAlonzo.Code.Relation.Binary.Core.C228 v8
                      -> coe
                           (\ v9 v10 v11 -> MAlonzo.Code.Relation.Binary.Core.C228 v11) erased
                           erased (coe (\ v9 v10 v11 -> C26 v11) erased erased v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe
                    (\ v4 v5 v6 -> MAlonzo.Code.Relation.Binary.Core.C212 v4)
                    (coe (\ v4 -> C30) erased) erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Maybe.Base.C30
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v3
               -> coe
                    (\ v4 v5 v6 -> MAlonzo.Code.Relation.Binary.Core.C228 v6) erased
                    erased (coe (\ v4 -> C30) erased)
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe
                    (\ v3 v4 v5 -> MAlonzo.Code.Relation.Binary.Core.C220 v4) erased
                    MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C22
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name354
  = "Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-irrefl"
d354 ::
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
  T20 -> MAlonzo.Code.Data.Empty.T4
d354 = erased
name362
  = "Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-respˡ-≈⁺"
d362 ::
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
  T20 -> T20
d362 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du362 v6 v7 v8 v9 v10 v11
du362 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  T20 -> T20
du362 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C22
        -> coe v5
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C28 v8
        -> case coe v5 of
             C26 v11
               -> case coe v1 of
                    MAlonzo.Code.Data.Maybe.Base.C28 v12
                      -> case coe v2 of
                           MAlonzo.Code.Data.Maybe.Base.C28 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Data.Maybe.Base.C28 v14
                                    -> coe
                                         (\ v15 v16 v17 -> C26 v17) erased erased
                                         (coe v0 v12 v13 v14 v8 v11)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C30 -> coe (\ v10 -> C30) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name380
  = "Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-respʳ-≈⁺"
d380 ::
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
  T20 -> T20
d380 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du380 v6 v7 v8 v9 v10 v11
du380 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  T20 -> T20
du380 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C22
        -> coe v5
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C28 v8
        -> case coe v5 of
             C26 v11
               -> case coe v1 of
                    MAlonzo.Code.Data.Maybe.Base.C28 v12
                      -> case coe v2 of
                           MAlonzo.Code.Data.Maybe.Base.C28 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Data.Maybe.Base.C28 v14
                                    -> coe
                                         (\ v15 v16 v17 -> C26 v17) erased erased
                                         (coe v0 v12 v13 v14 v8 v11)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name392
  = "Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-resp-≈⁺"
d392 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d392 v0 v1 v2 v3 v4 v5 = du392
du392 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du392
  = coe
      (MAlonzo.Code.Data.Product.du150 (coe du380) (coe (\ v0 -> du362)))
name394
  = "Relation.Binary.Construct.Add.Supremum.Strict.<⁺-isStrictPartialOrder-≡"
d394 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T570 ->
  MAlonzo.Code.Relation.Binary.T570
d394 v0 v1 v2 v3 v4 = du394 v4
du394 ::
  MAlonzo.Code.Relation.Binary.T570 ->
  MAlonzo.Code.Relation.Binary.T570
du394 v0
  = coe
      (\ v1 v2 v3 v4 -> MAlonzo.Code.Relation.Binary.C3423 v1 v3 v4)
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du70 erased
      (du48 (coe (MAlonzo.Code.Relation.Binary.d596 (coe v0)))) du254
name430
  = "Relation.Binary.Construct.Add.Supremum.Strict.<⁺-isDecStrictPartialOrder-≡"
d430 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T692 ->
  MAlonzo.Code.Relation.Binary.T692
d430 v0 v1 v2 v3 v4 = du430 v4
du430 ::
  MAlonzo.Code.Relation.Binary.T692 ->
  MAlonzo.Code.Relation.Binary.T692
du430 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C4393
         (coe (du394 (coe (MAlonzo.Code.Relation.Binary.d712 (coe v0)))))
         (coe
            (MAlonzo.Code.Data.Maybe.Properties.du24
               (coe (MAlonzo.Code.Relation.Binary.d714 (coe v0)))))
         (coe (du62 (coe (MAlonzo.Code.Relation.Binary.d716 (coe v0))))))
name478
  = "Relation.Binary.Construct.Add.Supremum.Strict.<⁺-isStrictTotalOrder-≡"
d478 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T1202 ->
  MAlonzo.Code.Relation.Binary.T1202
d478 v0 v1 v2 v3 v4 = du478 v4
du478 ::
  MAlonzo.Code.Relation.Binary.T1202 ->
  MAlonzo.Code.Relation.Binary.T1202
du478 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C7321
         (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du70)
         (coe (du48 (coe (MAlonzo.Code.Relation.Binary.d1224 (coe v0)))))
         (coe (du184 (coe (MAlonzo.Code.Relation.Binary.d1226 (coe v0))))))
name536 = "Relation.Binary.Construct.Add.Supremum.Strict._._._≈∙_"
d536 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name566
  = "Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-isStrictPartialOrder"
d566 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T570 ->
  MAlonzo.Code.Relation.Binary.T570
d566 v0 v1 v2 v3 v4 v5 v6 = du566 v6
du566 ::
  MAlonzo.Code.Relation.Binary.T570 ->
  MAlonzo.Code.Relation.Binary.T570
du566 v0
  = coe
      (\ v1 v2 v3 v4 -> MAlonzo.Code.Relation.Binary.C3423 v1 v3 v4)
      (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du108
         (coe (MAlonzo.Code.Relation.Binary.d592 (coe v0))))
      erased (du48 (coe (MAlonzo.Code.Relation.Binary.d596 (coe v0))))
      (coe du392 (MAlonzo.Code.Relation.Binary.d598 (coe v0)))
name602
  = "Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-isDecStrictPartialOrder"
d602 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T692 ->
  MAlonzo.Code.Relation.Binary.T692
d602 v0 v1 v2 v3 v4 v5 v6 = du602 v6
du602 ::
  MAlonzo.Code.Relation.Binary.T692 ->
  MAlonzo.Code.Relation.Binary.T692
du602 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C4393
         (coe (du566 (coe (MAlonzo.Code.Relation.Binary.d712 (coe v0)))))
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du66
               (coe (MAlonzo.Code.Relation.Binary.d714 (coe v0)))))
         (coe (du62 (coe (MAlonzo.Code.Relation.Binary.d716 (coe v0))))))
name650
  = "Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-isStrictTotalOrder"
d650 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T1202 ->
  MAlonzo.Code.Relation.Binary.T1202
d650 v0 v1 v2 v3 v4 v5 v6 = du650 v6
du650 ::
  MAlonzo.Code.Relation.Binary.T1202 ->
  MAlonzo.Code.Relation.Binary.T1202
du650 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C7321
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du108
               (coe (MAlonzo.Code.Relation.Binary.d1222 (coe v0)))))
         (coe (du48 (coe (MAlonzo.Code.Relation.Binary.d1224 (coe v0)))))
         (coe (du296 (coe (MAlonzo.Code.Relation.Binary.d1226 (coe v0))))))
name6853
  = "Relation.Binary.Construct.Add.Supremum.Strict..absurdlambda"
d6853 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d6853 = erased
name7145
  = "Relation.Binary.Construct.Add.Supremum.Strict..absurdlambda"
d7145 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  T20 -> MAlonzo.Code.Data.Empty.T4
d7145 = erased
name17711
  = "Relation.Binary.Construct.Add.Supremum.Strict..absurdlambda"
d17711 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  T20 -> MAlonzo.Code.Data.Empty.T4
d17711 = erased
name17841
  = "Relation.Binary.Construct.Add.Supremum.Strict..absurdlambda"
d17841 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  T20 -> MAlonzo.Code.Data.Empty.T4
d17841 = erased
name18251
  = "Relation.Binary.Construct.Add.Supremum.Strict..absurdlambda"
d18251 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d18251 = erased
name18291
  = "Relation.Binary.Construct.Add.Supremum.Strict..absurdlambda"
d18291 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Data.Empty.T4
d18291 = erased
name18513
  = "Relation.Binary.Construct.Add.Supremum.Strict..absurdlambda"
d18513 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Data.Empty.T4
d18513 = erased
name18751
  = "Relation.Binary.Construct.Add.Supremum.Strict..absurdlambda"
d18751 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d18751 = erased
name21999
  = "Relation.Binary.Construct.Add.Supremum.Strict._..absurdlambda"
d21999 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  T20 -> MAlonzo.Code.Data.Empty.T4
d21999 = erased
name22169
  = "Relation.Binary.Construct.Add.Supremum.Strict._..absurdlambda"
d22169 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  T20 -> MAlonzo.Code.Data.Empty.T4
d22169 = erased
name22695
  = "Relation.Binary.Construct.Add.Supremum.Strict._..absurdlambda"
d22695 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d22695 = erased
name22985
  = "Relation.Binary.Construct.Add.Supremum.Strict._..absurdlambda"
d22985 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Data.Empty.T4
d22985 = erased
name23403
  = "Relation.Binary.Construct.Add.Supremum.Strict._..absurdlambda"
d23403 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  MAlonzo.Code.Data.Empty.T4
d23403 = erased
name23697
  = "Relation.Binary.Construct.Add.Supremum.Strict._..absurdlambda"
d23697 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d23697 = erased
