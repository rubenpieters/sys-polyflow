{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict where

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
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary
import qualified MAlonzo.Code.Relation.Nullary.Decidable

name20 = "Relation.Binary.Construct.Add.Infimum.Strict._<₋_"
d20 a0 a1 a2 a3 a4 a5 = ()
data T20 = C24 | C30 AgdaAny
name36
  = "Relation.Binary.Construct.Add.Infimum.Strict.[<]-injective"
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
name40 = "Relation.Binary.Construct.Add.Infimum.Strict.<₋-asym"
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
name48 = "Relation.Binary.Construct.Add.Infimum.Strict.<₋-trans"
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
      C24 -> coe (seq (coe v5) (coe (\ v7 -> C24) erased))
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
name62 = "Relation.Binary.Construct.Add.Infimum.Strict.<₋-dec"
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
                    (coe (\ v5 v6 v7 -> C30 v7) erased erased) du36 (coe v0 v3 v4)
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe (\ v4 -> MAlonzo.Code.Relation.Nullary.C26) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Maybe.Base.C30
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v3
               -> coe
                    (MAlonzo.Code.Relation.Nullary.C22 (coe (\ v4 -> C24) erased))
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe (\ v3 -> MAlonzo.Code.Relation.Nullary.C26) erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name80
  = "Relation.Binary.Construct.Add.Infimum.Strict.<₋-irrelevant"
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
name102 = "Relation.Binary.Construct.Add.Infimum.Strict._._._≤₋_"
d102 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name154
  = "Relation.Binary.Construct.Add.Infimum.Strict._.<₋-transʳ"
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
  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.T20 ->
  T20 -> T20
d154 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du154 v6 v7 v8 v9 v10 v11
du154 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.T20 ->
  T20 -> T20
du154 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.C24
        -> coe (seq (coe v5) (coe (\ v7 -> C24) erased))
      MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.C30 v8
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
name172
  = "Relation.Binary.Construct.Add.Infimum.Strict._.<₋-transˡ"
d172 ::
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
  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.T20 ->
  T20
d172 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du172 v6 v7 v8 v9 v10 v11
du172 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.T20 ->
  T20
du172 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C24 -> coe (seq (coe v5) (coe (\ v7 -> C24) erased))
      C30 v8
        -> case coe v5 of
             MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.C30 v11
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
name186 = "Relation.Binary.Construct.Add.Infimum.Strict.<₋-cmp-≡"
d186 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Core.T198
d186 v0 v1 v2 v3 v4 v5 v6 = du186 v4 v5 v6
du186 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Core.T198
du186 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Maybe.Base.C28 v3
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v4
               -> let v5 = coe v0 v3 v4 in
                  case coe v5 of
                    MAlonzo.Code.Relation.Binary.Core.C212 v6
                      -> coe
                           (\ v9 v10 v11 -> MAlonzo.Code.Relation.Binary.Core.C212 v9)
                           (coe (\ v9 v10 v11 -> C30 v11) erased erased v6) erased erased
                    MAlonzo.Code.Relation.Binary.Core.C220 v7
                      -> coe
                           (\ v9 v10 v11 -> MAlonzo.Code.Relation.Binary.Core.C220 v10) erased
                           erased erased
                    MAlonzo.Code.Relation.Binary.Core.C228 v8
                      -> coe
                           (\ v9 v10 v11 -> MAlonzo.Code.Relation.Binary.Core.C228 v11) erased
                           erased (coe (\ v9 v10 v11 -> C30 v11) erased erased v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe
                    (\ v4 v5 v6 -> MAlonzo.Code.Relation.Binary.Core.C228 v6) erased
                    erased (coe (\ v4 -> C24) erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Maybe.Base.C30
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v3
               -> coe
                    (\ v4 v5 v6 -> MAlonzo.Code.Relation.Binary.Core.C212 v4)
                    (coe (\ v4 -> C24) erased) erased erased
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe
                    (\ v3 v4 v5 -> MAlonzo.Code.Relation.Binary.Core.C220 v4) erased
                    erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name242
  = "Relation.Binary.Construct.Add.Infimum.Strict.<₋-irrefl-≡"
d242 ::
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
d242 = erased
name248 = "Relation.Binary.Construct.Add.Infimum.Strict.<₋-respˡ-≡"
d248 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 -> T20 -> T20
d248 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du248 v8
du248 :: T20 -> T20
du248 v0 = coe v0
name252 = "Relation.Binary.Construct.Add.Infimum.Strict.<₋-respʳ-≡"
d252 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 -> T20 -> T20
d252 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du252 v8
du252 :: T20 -> T20
du252 v0 = coe v0
name256 = "Relation.Binary.Construct.Add.Infimum.Strict.<₋-resp-≡"
d256 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d256 v0 v1 v2 v3 = du256
du256 :: MAlonzo.Code.Agda.Builtin.Sigma.T14
du256
  = coe
      (MAlonzo.Code.Agda.Builtin.Sigma.C32
         (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4)))
name268 = "Relation.Binary.Construct.Add.Infimum.Strict._._._≈∙_"
d268 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name298 = "Relation.Binary.Construct.Add.Infimum.Strict._.<₋-cmp"
d298 ::
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
d298 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du298 v6 v7 v8
du298 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Core.T198
du298 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Maybe.Base.C28 v3
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v4
               -> let v5 = coe v0 v3 v4 in
                  case coe v5 of
                    MAlonzo.Code.Relation.Binary.Core.C212 v6
                      -> coe
                           (\ v9 v10 v11 -> MAlonzo.Code.Relation.Binary.Core.C212 v9)
                           (coe (\ v9 v10 v11 -> C30 v11) erased erased v6) erased erased
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
                           erased (coe (\ v9 v10 v11 -> C30 v11) erased erased v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe
                    (\ v4 v5 v6 -> MAlonzo.Code.Relation.Binary.Core.C228 v6) erased
                    erased (coe (\ v4 -> C24) erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Maybe.Base.C30
        -> case coe v2 of
             MAlonzo.Code.Data.Maybe.Base.C28 v3
               -> coe
                    (\ v4 v5 v6 -> MAlonzo.Code.Relation.Binary.Core.C212 v4)
                    (coe (\ v4 -> C24) erased) erased erased
             MAlonzo.Code.Data.Maybe.Base.C30
               -> coe
                    (\ v3 v4 v5 -> MAlonzo.Code.Relation.Binary.Core.C220 v4) erased
                    MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C22
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name356
  = "Relation.Binary.Construct.Add.Infimum.Strict._.<₋-irrefl"
d356 ::
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
d356 = erased
name364
  = "Relation.Binary.Construct.Add.Infimum.Strict._.<₋-respˡ-≈₋"
d364 ::
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
d364 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du364 v6 v7 v8 v9 v10 v11
du364 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  T20 -> T20
du364 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C22
        -> coe v5
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C28 v8
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
name376
  = "Relation.Binary.Construct.Add.Infimum.Strict._.<₋-respʳ-≈₋"
d376 ::
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
d376 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du376 v6 v7 v8 v9 v10 v11
du376 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T20 ->
  T20 -> T20
du376 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C22
        -> coe v5
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C28 v8
        -> case coe v5 of
             C24 -> coe (\ v10 -> C24) erased
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
name394
  = "Relation.Binary.Construct.Add.Infimum.Strict._.<₋-resp-≈₋"
d394 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d394 v0 v1 v2 v3 v4 v5 = du394
du394 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du394
  = coe
      (MAlonzo.Code.Data.Product.du150 (coe du376) (coe (\ v0 -> du364)))
name396
  = "Relation.Binary.Construct.Add.Infimum.Strict.<₋-isStrictPartialOrder-≡"
d396 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T570 ->
  MAlonzo.Code.Relation.Binary.T570
d396 v0 v1 v2 v3 v4 = du396 v4
du396 ::
  MAlonzo.Code.Relation.Binary.T570 ->
  MAlonzo.Code.Relation.Binary.T570
du396 v0
  = coe
      (\ v1 v2 v3 v4 -> MAlonzo.Code.Relation.Binary.C3423 v1 v3 v4)
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du70 erased
      (du48 (coe (MAlonzo.Code.Relation.Binary.d596 (coe v0)))) du256
name432
  = "Relation.Binary.Construct.Add.Infimum.Strict.<₋-isDecStrictPartialOrder-≡"
d432 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T692 ->
  MAlonzo.Code.Relation.Binary.T692
d432 v0 v1 v2 v3 v4 = du432 v4
du432 ::
  MAlonzo.Code.Relation.Binary.T692 ->
  MAlonzo.Code.Relation.Binary.T692
du432 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C4393
         (coe (du396 (coe (MAlonzo.Code.Relation.Binary.d712 (coe v0)))))
         (coe
            (MAlonzo.Code.Data.Maybe.Properties.du24
               (coe (MAlonzo.Code.Relation.Binary.d714 (coe v0)))))
         (coe (du62 (coe (MAlonzo.Code.Relation.Binary.d716 (coe v0))))))
name480
  = "Relation.Binary.Construct.Add.Infimum.Strict.<₋-isStrictTotalOrder-≡"
d480 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T1202 ->
  MAlonzo.Code.Relation.Binary.T1202
d480 v0 v1 v2 v3 v4 = du480 v4
du480 ::
  MAlonzo.Code.Relation.Binary.T1202 ->
  MAlonzo.Code.Relation.Binary.T1202
du480 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C7321
         (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du70)
         (coe (du48 (coe (MAlonzo.Code.Relation.Binary.d1224 (coe v0)))))
         (coe (du186 (coe (MAlonzo.Code.Relation.Binary.d1226 (coe v0))))))
name538 = "Relation.Binary.Construct.Add.Infimum.Strict._._._≈∙_"
d538 a0 a1 a2 a3 a4 a5 a6 a7 = ()
name568
  = "Relation.Binary.Construct.Add.Infimum.Strict._.<₋-isStrictPartialOrder"
d568 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T570 ->
  MAlonzo.Code.Relation.Binary.T570
d568 v0 v1 v2 v3 v4 v5 v6 = du568 v6
du568 ::
  MAlonzo.Code.Relation.Binary.T570 ->
  MAlonzo.Code.Relation.Binary.T570
du568 v0
  = coe
      (\ v1 v2 v3 v4 -> MAlonzo.Code.Relation.Binary.C3423 v1 v3 v4)
      (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du108
         (coe (MAlonzo.Code.Relation.Binary.d592 (coe v0))))
      erased (du48 (coe (MAlonzo.Code.Relation.Binary.d596 (coe v0))))
      (coe du394 (MAlonzo.Code.Relation.Binary.d598 (coe v0)))
name604
  = "Relation.Binary.Construct.Add.Infimum.Strict._.<₋-isDecStrictPartialOrder"
d604 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T692 ->
  MAlonzo.Code.Relation.Binary.T692
d604 v0 v1 v2 v3 v4 v5 v6 = du604 v6
du604 ::
  MAlonzo.Code.Relation.Binary.T692 ->
  MAlonzo.Code.Relation.Binary.T692
du604 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C4393
         (coe (du568 (coe (MAlonzo.Code.Relation.Binary.d712 (coe v0)))))
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du66
               (coe (MAlonzo.Code.Relation.Binary.d714 (coe v0)))))
         (coe (du62 (coe (MAlonzo.Code.Relation.Binary.d716 (coe v0))))))
name652
  = "Relation.Binary.Construct.Add.Infimum.Strict._.<₋-isStrictTotalOrder"
d652 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T1202 ->
  MAlonzo.Code.Relation.Binary.T1202
d652 v0 v1 v2 v3 v4 v5 v6 = du652 v6
du652 ::
  MAlonzo.Code.Relation.Binary.T1202 ->
  MAlonzo.Code.Relation.Binary.T1202
du652 v0
  = coe
      (MAlonzo.Code.Relation.Binary.C7321
         (coe
            (MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du108
               (coe (MAlonzo.Code.Relation.Binary.d1222 (coe v0)))))
         (coe (du48 (coe (MAlonzo.Code.Relation.Binary.d1224 (coe v0)))))
         (coe (du298 (coe (MAlonzo.Code.Relation.Binary.d1226 (coe v0))))))
name5843
  = "Relation.Binary.Construct.Add.Infimum.Strict..absurdlambda"
d5843 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  T20 -> MAlonzo.Code.Data.Empty.T4
d5843 = erased
name6277
  = "Relation.Binary.Construct.Add.Infimum.Strict..absurdlambda"
d6277 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d6277 = erased
name16681
  = "Relation.Binary.Construct.Add.Infimum.Strict..absurdlambda"
d16681 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  T20 -> MAlonzo.Code.Data.Empty.T4
d16681 = erased
name16751
  = "Relation.Binary.Construct.Add.Infimum.Strict..absurdlambda"
d16751 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  T20 -> MAlonzo.Code.Data.Empty.T4
d16751 = erased
name16963
  = "Relation.Binary.Construct.Add.Infimum.Strict..absurdlambda"
d16963 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Data.Empty.T4
d16963 = erased
name17043
  = "Relation.Binary.Construct.Add.Infimum.Strict..absurdlambda"
d17043 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d17043 = erased
name17305
  = "Relation.Binary.Construct.Add.Infimum.Strict..absurdlambda"
d17305 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d17305 = erased
name17345
  = "Relation.Binary.Construct.Add.Infimum.Strict..absurdlambda"
d17345 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Data.Empty.T4
d17345 = erased
name20513
  = "Relation.Binary.Construct.Add.Infimum.Strict._..absurdlambda"
d20513 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  T20 -> MAlonzo.Code.Data.Empty.T4
d20513 = erased
name20603
  = "Relation.Binary.Construct.Add.Infimum.Strict._..absurdlambda"
d20603 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  T20 -> MAlonzo.Code.Data.Empty.T4
d20603 = erased
name21125
  = "Relation.Binary.Construct.Add.Infimum.Strict._..absurdlambda"
d21125 ::
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
d21125 = erased
name21225
  = "Relation.Binary.Construct.Add.Infimum.Strict._..absurdlambda"
d21225 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d21225 = erased
name21567
  = "Relation.Binary.Construct.Add.Infimum.Strict._..absurdlambda"
d21567 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T198) ->
  AgdaAny -> T20 -> MAlonzo.Code.Data.Empty.T4
d21567 = erased
name21743
  = "Relation.Binary.Construct.Add.Infimum.Strict._..absurdlambda"
d21743 ::
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
d21743 = erased
