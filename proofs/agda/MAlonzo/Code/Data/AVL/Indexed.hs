{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.AVL.Indexed where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.AVL.Height
import qualified MAlonzo.Code.Data.AVL.Key
import qualified MAlonzo.Code.Data.AVL.Value
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict
import qualified MAlonzo.Code.Relation.Binary.Core

name78 = "Data.AVL.Indexed._._<_<_"
d78 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  AgdaAny -> MAlonzo.Code.Data.Maybe.Base.T22 -> ()
d78 = erased
name80 = "Data.AVL.Indexed._._<⁺_"
d80 a0 a1 a2 a3 a4 a5 = ()
name82 = "Data.AVL.Indexed._.Key⁺"
d82 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 -> ()
d82 = erased
name84 = "Data.AVL.Indexed._.trans⁺"
d84 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
d84 v0 v1 v2 v3 = du84 v3
du84 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20
du84 v0 = coe (MAlonzo.Code.Data.AVL.Key.du108 (coe v0))
name86 = "Data.AVL.Indexed._.⊥⁺<[_]<⊤⁺"
d86 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d86 v0 v1 = du86
du86 :: MAlonzo.Code.Agda.Builtin.Sigma.T14
du86
  = coe
      (MAlonzo.Code.Agda.Builtin.Sigma.C32
         (coe
            (\ v0 v1 v2 ->
               MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26 v2)
            erased erased
            (coe
               (\ v0 ->
                  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C24)
               erased))
         (coe
            (\ v0 ->
               MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
            erased))
name96 = "Data.AVL.Indexed._.Extrema.[_]-injective"
d96 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d96 = erased
name102 = "Data.AVL.Indexed._.Value"
d102 a0 a1 a2 a3 a4 = ()
name104 = "Data.AVL.Indexed._.const"
d104 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Data.AVL.Value.T36
d104 v0 v1 v2 v3 = du104
du104 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Data.AVL.Value.T36
du104 = coe (\ v0 v1 -> MAlonzo.Code.Data.AVL.Value.du52)
name108 = "Data.AVL.Indexed._.Value.family"
d108 :: MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> ()
d108 = erased
name110 = "Data.AVL.Indexed._.Value.respects"
d110 ::
  MAlonzo.Code.Data.AVL.Value.T36 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d110 = coe MAlonzo.Code.Data.AVL.Value.d46
name118 = "Data.AVL.Indexed.K&_"
d118 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> ()
d118 = erased
name130 = "Data.AVL.Indexed.Tree"
d130 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T130
  = C142 MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 |
    C158 Integer Integer MAlonzo.Code.Agda.Builtin.Sigma.T14 T130 T130
         MAlonzo.Code.Data.AVL.Height.T28
name168 = "Data.AVL.Indexed._.Val"
d168 :: MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> ()
d168 = erased
name170 = "Data.AVL.Indexed._.V≈"
d170 ::
  MAlonzo.Code.Data.AVL.Value.T36 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d170 v0 = coe (MAlonzo.Code.Data.AVL.Value.d46 (coe v0))
name180 = "Data.AVL.Indexed._.leaf-injective"
d180 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d180 = erased
name212 = "Data.AVL.Indexed._.node-injective-key"
d212 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  T130 ->
  T130 ->
  T130 ->
  T130 ->
  MAlonzo.Code.Data.AVL.Height.T28 ->
  MAlonzo.Code.Data.AVL.Height.T28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d212 = erased
name222 = "Data.AVL.Indexed._.castˡ"
d222 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  T130 -> T130
d222 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du222 v3 v6 v7 v8 v10 v11
du222 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  T130 -> T130
du222 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C142 v6
        -> coe
             (C142 (coe MAlonzo.Code.Data.AVL.Key.du108 v0 v1 v2 v3 v4 v6))
      C158 v6 v7 v9 v10 v11 v12
        -> coe
             (\ v13 v14 v15 v16 v17 v18 v19 -> C158 v13 v14 v16 v17 v18 v19) v6
             v7 erased v9
             (du222
                (coe v0) (coe v1) (coe v2)
                (coe
                   (MAlonzo.Code.Data.Maybe.Base.C28
                      (coe
                         (MAlonzo.Code.Data.Maybe.Base.C28
                            (coe (MAlonzo.Code.Agda.Builtin.Sigma.d28 (coe v9)))))))
                (coe v4) (coe v10))
             v11 v12
      _ -> MAlonzo.RTE.mazUnreachableError
name248 = "Data.AVL.Indexed._.castʳ"
d248 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer ->
  T130 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  T130
d248 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du248 v3 v6 v7 v8 v10 v11
du248 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  T130 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  T130
du248 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C142 v6
        -> coe
             (C142 (coe MAlonzo.Code.Data.AVL.Key.du108 v0 v1 v2 v3 v6 v5))
      C158 v6 v7 v9 v10 v11 v12
        -> coe
             (\ v13 v14 v15 v16 v17 v18 v19 -> C158 v13 v14 v16 v17 v18 v19) v6
             v7 erased v9 v10
             (du248
                (coe v0)
                (coe
                   (MAlonzo.Code.Data.Maybe.Base.C28
                      (coe
                         (MAlonzo.Code.Data.Maybe.Base.C28
                            (coe (MAlonzo.Code.Agda.Builtin.Sigma.d28 (coe v9)))))))
                (coe v2) (coe v3) (coe v11) (coe v5))
             v12
      _ -> MAlonzo.RTE.mazUnreachableError
name284 = "Data.AVL.Indexed._.joinˡ⁺"
d284 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  T130 ->
  MAlonzo.Code.Data.AVL.Height.T28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d284 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = du284 v8 v9 v11 v12 v13 v14
du284 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  T130 ->
  MAlonzo.Code.Data.AVL.Height.T28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du284 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C32 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Data.Fin.Base.C10
               -> coe
                    (MAlonzo.Code.Agda.Builtin.Sigma.C32
                       (coe (\ v9 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                       (coe
                          (\ v9 v10 v11 v12 v13 v14 v15 -> C158 v9 v10 v12 v13 v14 v15)
                          (MAlonzo.Code.Data.AVL.Height.d14
                             (coe (\ v9 -> MAlonzo.Code.Data.Fin.Base.C10) erased) (coe v0))
                          v1 erased v2 v7 v4 v5))
             MAlonzo.Code.Data.Fin.Base.C16 v9
               -> coe
                    (seq
                       (coe v9)
                       (case coe v7 of
                          C158 v10 v11 v13 v14 v15 v16
                            -> let v17
                                     = let v17
                                             = case coe v5 of
                                                 MAlonzo.Code.Data.AVL.Height.C32
                                                   -> coe
                                                        (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                           (coe
                                                              (\ v18 ->
                                                                 MAlonzo.Code.Data.Fin.Base.C10)
                                                              erased)
                                                           (coe
                                                              (\ v18 v19 v20 v21 v22 v23 v24 ->
                                                                 C158 v18 v19 v21 v22 v23 v24)
                                                              (MAlonzo.Code.Data.AVL.Height.d14
                                                                 (coe
                                                                    (\ v18 v19 ->
                                                                       MAlonzo.Code.Data.Fin.Base.C16
                                                                         v19)
                                                                    erased
                                                                    (coe
                                                                       (\ v18 ->
                                                                          MAlonzo.Code.Data.Fin.Base.C10)
                                                                       erased))
                                                                 (coe v0))
                                                              (addInt (coe (1 :: Integer)) (coe v0))
                                                              erased v2
                                                              (coe
                                                                 (\ v18 v19 v20 v21 v22 v23 v24 ->
                                                                    C158 v18 v19 v21 v22 v23 v24)
                                                                 v10 v11 erased v13 v14 v15 v16)
                                                              v4
                                                              (coe
                                                                 (\ v18 ->
                                                                    MAlonzo.Code.Data.AVL.Height.C36)
                                                                 erased)))
                                                 MAlonzo.Code.Data.AVL.Height.C36
                                                   -> coe
                                                        (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                           (coe
                                                              (\ v18 v19 ->
                                                                 MAlonzo.Code.Data.Fin.Base.C16 v19)
                                                              erased
                                                              (coe
                                                                 (\ v18 ->
                                                                    MAlonzo.Code.Data.Fin.Base.C10)
                                                                 erased))
                                                           (coe
                                                              (\ v18 v19 v20 v21 v22 v23 v24 ->
                                                                 C158 v18 v19 v21 v22 v23 v24)
                                                              (MAlonzo.Code.Data.AVL.Height.d14
                                                                 (coe
                                                                    (\ v18 v19 ->
                                                                       MAlonzo.Code.Data.Fin.Base.C16
                                                                         v19)
                                                                    erased
                                                                    (coe
                                                                       (\ v18 ->
                                                                          MAlonzo.Code.Data.Fin.Base.C10)
                                                                       erased))
                                                                 (coe v0))
                                                              v0 erased v2
                                                              (coe
                                                                 (\ v18 v19 v20 v21 v22 v23 v24 ->
                                                                    C158 v18 v19 v21 v22 v23 v24)
                                                                 v10 v11 erased v13 v14 v15 v16)
                                                              v4
                                                              (coe
                                                                 (\ v18 ->
                                                                    MAlonzo.Code.Data.AVL.Height.C40)
                                                                 erased)))
                                                 _ -> MAlonzo.RTE.mazUnreachableError in
                                       case coe v16 of
                                         MAlonzo.Code.Data.AVL.Height.C36
                                           -> case coe v5 of
                                                MAlonzo.Code.Data.AVL.Height.C40
                                                  -> coe
                                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                          (coe
                                                             (\ v20 v21 ->
                                                                MAlonzo.Code.Data.Fin.Base.C16 v21)
                                                             erased
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.Fin.Base.C10)
                                                                erased))
                                                          (coe
                                                             (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                C158 v20 v21 v23 v24 v25 v26)
                                                             (addInt (coe (1 :: Integer)) (coe v1))
                                                             (addInt (coe (2 :: Integer)) (coe v1))
                                                             erased v13 v14
                                                             (coe
                                                                (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                   C158 v20 v21 v23 v24 v25 v26)
                                                                (addInt
                                                                   (coe (1 :: Integer)) (coe v1))
                                                                v1 erased v2 v15 v4
                                                                (coe
                                                                   (\ v20 ->
                                                                      MAlonzo.Code.Data.AVL.Height.C40)
                                                                   erased))
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.AVL.Height.C32)
                                                                erased)))
                                                MAlonzo.Code.Data.AVL.Height.C32
                                                  -> coe
                                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                          (coe
                                                             (\ v20 ->
                                                                MAlonzo.Code.Data.Fin.Base.C10)
                                                             erased)
                                                          (coe
                                                             (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                C158 v20 v21 v23 v24 v25 v26)
                                                             (MAlonzo.Code.Data.AVL.Height.d14
                                                                (coe
                                                                   (\ v20 v21 ->
                                                                      MAlonzo.Code.Data.Fin.Base.C16
                                                                        v21)
                                                                   erased
                                                                   (coe
                                                                      (\ v20 ->
                                                                         MAlonzo.Code.Data.Fin.Base.C10)
                                                                      erased))
                                                                (coe v0))
                                                             (addInt (coe (1 :: Integer)) (coe v0))
                                                             erased v2
                                                             (coe
                                                                (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                   C158 v20 v21 v23 v24 v25 v26)
                                                                v10 v11 erased v13 v14 v15
                                                                (coe
                                                                   (\ v20 ->
                                                                      MAlonzo.Code.Data.AVL.Height.C36)
                                                                   erased))
                                                             v4
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.AVL.Height.C36)
                                                                erased)))
                                                MAlonzo.Code.Data.AVL.Height.C36
                                                  -> coe
                                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                          (coe
                                                             (\ v20 v21 ->
                                                                MAlonzo.Code.Data.Fin.Base.C16 v21)
                                                             erased
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.Fin.Base.C10)
                                                                erased))
                                                          (coe
                                                             (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                C158 v20 v21 v23 v24 v25 v26)
                                                             (MAlonzo.Code.Data.AVL.Height.d14
                                                                (coe
                                                                   (\ v20 v21 ->
                                                                      MAlonzo.Code.Data.Fin.Base.C16
                                                                        v21)
                                                                   erased
                                                                   (coe
                                                                      (\ v20 ->
                                                                         MAlonzo.Code.Data.Fin.Base.C10)
                                                                      erased))
                                                                (coe v0))
                                                             v0 erased v2
                                                             (coe
                                                                (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                   C158 v20 v21 v23 v24 v25 v26)
                                                                v10 v11 erased v13 v14 v15
                                                                (coe
                                                                   (\ v20 ->
                                                                      MAlonzo.Code.Data.AVL.Height.C36)
                                                                   erased))
                                                             v4
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.AVL.Height.C40)
                                                                erased)))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Data.AVL.Height.C40
                                           -> case coe v5 of
                                                MAlonzo.Code.Data.AVL.Height.C40
                                                  -> coe
                                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                          (coe
                                                             (\ v20 ->
                                                                MAlonzo.Code.Data.Fin.Base.C10)
                                                             erased)
                                                          (coe
                                                             (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                C158 v20 v21 v23 v24 v25 v26)
                                                             (addInt (coe (1 :: Integer)) (coe v11))
                                                             (addInt (coe (1 :: Integer)) (coe v11))
                                                             erased v13 v14
                                                             (coe
                                                                (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                   C158 v20 v21 v23 v24 v25 v26)
                                                                v11 v11 erased v2 v15 v4
                                                                (coe
                                                                   (\ v20 ->
                                                                      MAlonzo.Code.Data.AVL.Height.C36)
                                                                   erased))
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.AVL.Height.C36)
                                                                erased)))
                                                MAlonzo.Code.Data.AVL.Height.C32
                                                  -> coe
                                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                          (coe
                                                             (\ v20 ->
                                                                MAlonzo.Code.Data.Fin.Base.C10)
                                                             erased)
                                                          (coe
                                                             (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                C158 v20 v21 v23 v24 v25 v26)
                                                             (MAlonzo.Code.Data.AVL.Height.d14
                                                                (coe
                                                                   (\ v20 v21 ->
                                                                      MAlonzo.Code.Data.Fin.Base.C16
                                                                        v21)
                                                                   erased
                                                                   (coe
                                                                      (\ v20 ->
                                                                         MAlonzo.Code.Data.Fin.Base.C10)
                                                                      erased))
                                                                (coe v0))
                                                             (addInt (coe (1 :: Integer)) (coe v0))
                                                             erased v2
                                                             (coe
                                                                (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                   C158 v20 v21 v23 v24 v25 v26)
                                                                v10 v11 erased v13 v14 v15
                                                                (coe
                                                                   (\ v20 ->
                                                                      MAlonzo.Code.Data.AVL.Height.C40)
                                                                   erased))
                                                             v4
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.AVL.Height.C36)
                                                                erased)))
                                                MAlonzo.Code.Data.AVL.Height.C36
                                                  -> coe
                                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                          (coe
                                                             (\ v20 v21 ->
                                                                MAlonzo.Code.Data.Fin.Base.C16 v21)
                                                             erased
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.Fin.Base.C10)
                                                                erased))
                                                          (coe
                                                             (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                C158 v20 v21 v23 v24 v25 v26)
                                                             (MAlonzo.Code.Data.AVL.Height.d14
                                                                (coe
                                                                   (\ v20 v21 ->
                                                                      MAlonzo.Code.Data.Fin.Base.C16
                                                                        v21)
                                                                   erased
                                                                   (coe
                                                                      (\ v20 ->
                                                                         MAlonzo.Code.Data.Fin.Base.C10)
                                                                      erased))
                                                                (coe v0))
                                                             v0 erased v2
                                                             (coe
                                                                (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                   C158 v20 v21 v23 v24 v25 v26)
                                                                v10 v11 erased v13 v14 v15
                                                                (coe
                                                                   (\ v20 ->
                                                                      MAlonzo.Code.Data.AVL.Height.C40)
                                                                   erased))
                                                             v4
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.AVL.Height.C40)
                                                                erased)))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> coe v17 in
                               case coe v15 of
                                 C158 v18 v19 v21 v22 v23 v24
                                   -> case coe v16 of
                                        MAlonzo.Code.Data.AVL.Height.C32
                                          -> case coe v5 of
                                               MAlonzo.Code.Data.AVL.Height.C40
                                                 -> coe
                                                      (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                         (coe
                                                            (\ v27 ->
                                                               MAlonzo.Code.Data.Fin.Base.C10)
                                                            erased)
                                                         (coe
                                                            (\ v27 v28 v29 v30 v31 v32 v33 ->
                                                               C158 v27 v28 v30 v31 v32 v33)
                                                            (addInt (coe (1 :: Integer)) (coe v1))
                                                            (addInt (coe (1 :: Integer)) (coe v1))
                                                            erased v21
                                                            (coe
                                                               (\ v27 v28 v29 v30 v31 v32 v33 ->
                                                                  C158 v27 v28 v30 v31 v32 v33)
                                                               v1 v18 erased v13 v14 v22
                                                               (MAlonzo.Code.Data.AVL.Height.du48
                                                                  (coe v24)))
                                                            (coe
                                                               (\ v27 v28 v29 v30 v31 v32 v33 ->
                                                                  C158 v27 v28 v30 v31 v32 v33)
                                                               v19 v1 erased v2 v23 v4
                                                               (MAlonzo.Code.Data.AVL.Height.du56
                                                                  (coe v24)))
                                                            (coe
                                                               (\ v27 ->
                                                                  MAlonzo.Code.Data.AVL.Height.C36)
                                                               erased)))
                                               _ -> coe v17
                                        _ -> coe v17
                                 _ -> coe v17
                          _ -> case coe v5 of
                                 MAlonzo.Code.Data.AVL.Height.C32
                                   -> coe
                                        (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                           (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                           (coe
                                              (\ v11 v12 v13 v14 v15 v16 v17 ->
                                                 C158 v11 v12 v14 v15 v16 v17)
                                              (MAlonzo.Code.Data.AVL.Height.d14
                                                 (coe
                                                    (\ v11 v12 ->
                                                       MAlonzo.Code.Data.Fin.Base.C16 v12)
                                                    erased
                                                    (coe
                                                       (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10)
                                                       erased))
                                                 (coe v0))
                                              (addInt (coe (1 :: Integer)) (coe v0)) erased v2 v7 v4
                                              (coe
                                                 (\ v11 -> MAlonzo.Code.Data.AVL.Height.C36)
                                                 erased)))
                                 MAlonzo.Code.Data.AVL.Height.C36
                                   -> coe
                                        (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                           (coe
                                              (\ v11 v12 -> MAlonzo.Code.Data.Fin.Base.C16 v12)
                                              erased
                                              (coe
                                                 (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                           (coe
                                              (\ v11 v12 v13 v14 v15 v16 v17 ->
                                                 C158 v11 v12 v14 v15 v16 v17)
                                              (MAlonzo.Code.Data.AVL.Height.d14
                                                 (coe
                                                    (\ v11 v12 ->
                                                       MAlonzo.Code.Data.Fin.Base.C16 v12)
                                                    erased
                                                    (coe
                                                       (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10)
                                                       erased))
                                                 (coe v0))
                                              v0 erased v2 v7 v4
                                              (coe
                                                 (\ v11 -> MAlonzo.Code.Data.AVL.Height.C40)
                                                 erased)))
                                 _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name360 = "Data.AVL.Indexed._.joinʳ⁺"
d360 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  T130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Data.AVL.Height.T28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d360 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = du360 v8 v9 v11 v12 v13 v14
du360 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  T130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Data.AVL.Height.T28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du360 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C32 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Data.Fin.Base.C10
               -> coe
                    (MAlonzo.Code.Agda.Builtin.Sigma.C32
                       (coe (\ v9 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                       (coe
                          (\ v9 v10 v11 v12 v13 v14 v15 -> C158 v9 v10 v12 v13 v14 v15) v0
                          (MAlonzo.Code.Data.AVL.Height.d14
                             (coe (\ v9 -> MAlonzo.Code.Data.Fin.Base.C10) erased) (coe v1))
                          erased v2 v3 v7 v5))
             MAlonzo.Code.Data.Fin.Base.C16 v9
               -> coe
                    (seq
                       (coe v9)
                       (case coe v7 of
                          C158 v10 v11 v13 v14 v15 v16
                            -> let v17
                                     = let v17
                                             = case coe v5 of
                                                 MAlonzo.Code.Data.AVL.Height.C36
                                                   -> coe
                                                        (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                           (coe
                                                              (\ v18 v19 ->
                                                                 MAlonzo.Code.Data.Fin.Base.C16 v19)
                                                              erased
                                                              (coe
                                                                 (\ v18 ->
                                                                    MAlonzo.Code.Data.Fin.Base.C10)
                                                                 erased))
                                                           (coe
                                                              (\ v18 v19 v20 v21 v22 v23 v24 ->
                                                                 C158 v18 v19 v21 v22 v23 v24)
                                                              v0
                                                              (MAlonzo.Code.Data.AVL.Height.d14
                                                                 (coe
                                                                    (\ v18 v19 ->
                                                                       MAlonzo.Code.Data.Fin.Base.C16
                                                                         v19)
                                                                    erased
                                                                    (coe
                                                                       (\ v18 ->
                                                                          MAlonzo.Code.Data.Fin.Base.C10)
                                                                       erased))
                                                                 (coe v0))
                                                              erased v2 v3
                                                              (coe
                                                                 (\ v18 v19 v20 v21 v22 v23 v24 ->
                                                                    C158 v18 v19 v21 v22 v23 v24)
                                                                 v10 v11 erased v13 v14 v15 v16)
                                                              (coe
                                                                 (\ v18 ->
                                                                    MAlonzo.Code.Data.AVL.Height.C32)
                                                                 erased)))
                                                 MAlonzo.Code.Data.AVL.Height.C40
                                                   -> coe
                                                        (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                           (coe
                                                              (\ v18 ->
                                                                 MAlonzo.Code.Data.Fin.Base.C10)
                                                              erased)
                                                           (coe
                                                              (\ v18 v19 v20 v21 v22 v23 v24 ->
                                                                 C158 v18 v19 v21 v22 v23 v24)
                                                              (addInt (coe (1 :: Integer)) (coe v1))
                                                              (MAlonzo.Code.Data.AVL.Height.d14
                                                                 (coe
                                                                    (\ v18 v19 ->
                                                                       MAlonzo.Code.Data.Fin.Base.C16
                                                                         v19)
                                                                    erased
                                                                    (coe
                                                                       (\ v18 ->
                                                                          MAlonzo.Code.Data.Fin.Base.C10)
                                                                       erased))
                                                                 (coe v1))
                                                              erased v2 v3
                                                              (coe
                                                                 (\ v18 v19 v20 v21 v22 v23 v24 ->
                                                                    C158 v18 v19 v21 v22 v23 v24)
                                                                 v10 v11 erased v13 v14 v15 v16)
                                                              (coe
                                                                 (\ v18 ->
                                                                    MAlonzo.Code.Data.AVL.Height.C36)
                                                                 erased)))
                                                 _ -> MAlonzo.RTE.mazUnreachableError in
                                       case coe v16 of
                                         MAlonzo.Code.Data.AVL.Height.C32
                                           -> case coe v5 of
                                                MAlonzo.Code.Data.AVL.Height.C32
                                                  -> coe
                                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                          (coe
                                                             (\ v20 ->
                                                                MAlonzo.Code.Data.Fin.Base.C10)
                                                             erased)
                                                          (coe
                                                             (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                C158 v20 v21 v23 v24 v25 v26)
                                                             (addInt (coe (1 :: Integer)) (coe v10))
                                                             (addInt (coe (1 :: Integer)) (coe v10))
                                                             erased v13
                                                             (coe
                                                                (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                   C158 v20 v21 v23 v24 v25 v26)
                                                                v10 v10 erased v2 v3 v14
                                                                (coe
                                                                   (\ v20 ->
                                                                      MAlonzo.Code.Data.AVL.Height.C36)
                                                                   erased))
                                                             v15
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.AVL.Height.C36)
                                                                erased)))
                                                MAlonzo.Code.Data.AVL.Height.C36
                                                  -> coe
                                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                          (coe
                                                             (\ v20 v21 ->
                                                                MAlonzo.Code.Data.Fin.Base.C16 v21)
                                                             erased
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.Fin.Base.C10)
                                                                erased))
                                                          (coe
                                                             (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                C158 v20 v21 v23 v24 v25 v26)
                                                             v0
                                                             (MAlonzo.Code.Data.AVL.Height.d14
                                                                (coe
                                                                   (\ v20 v21 ->
                                                                      MAlonzo.Code.Data.Fin.Base.C16
                                                                        v21)
                                                                   erased
                                                                   (coe
                                                                      (\ v20 ->
                                                                         MAlonzo.Code.Data.Fin.Base.C10)
                                                                      erased))
                                                                (coe v0))
                                                             erased v2 v3
                                                             (coe
                                                                (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                   C158 v20 v21 v23 v24 v25 v26)
                                                                v10 v11 erased v13 v14 v15
                                                                (coe
                                                                   (\ v20 ->
                                                                      MAlonzo.Code.Data.AVL.Height.C32)
                                                                   erased))
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.AVL.Height.C32)
                                                                erased)))
                                                MAlonzo.Code.Data.AVL.Height.C40
                                                  -> coe
                                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                          (coe
                                                             (\ v20 ->
                                                                MAlonzo.Code.Data.Fin.Base.C10)
                                                             erased)
                                                          (coe
                                                             (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                C158 v20 v21 v23 v24 v25 v26)
                                                             (addInt (coe (1 :: Integer)) (coe v1))
                                                             (MAlonzo.Code.Data.AVL.Height.d14
                                                                (coe
                                                                   (\ v20 v21 ->
                                                                      MAlonzo.Code.Data.Fin.Base.C16
                                                                        v21)
                                                                   erased
                                                                   (coe
                                                                      (\ v20 ->
                                                                         MAlonzo.Code.Data.Fin.Base.C10)
                                                                      erased))
                                                                (coe v1))
                                                             erased v2 v3
                                                             (coe
                                                                (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                   C158 v20 v21 v23 v24 v25 v26)
                                                                v10 v11 erased v13 v14 v15
                                                                (coe
                                                                   (\ v20 ->
                                                                      MAlonzo.Code.Data.AVL.Height.C32)
                                                                   erased))
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.AVL.Height.C36)
                                                                erased)))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Data.AVL.Height.C36
                                           -> case coe v5 of
                                                MAlonzo.Code.Data.AVL.Height.C32
                                                  -> coe
                                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                          (coe
                                                             (\ v20 v21 ->
                                                                MAlonzo.Code.Data.Fin.Base.C16 v21)
                                                             erased
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.Fin.Base.C10)
                                                                erased))
                                                          (coe
                                                             (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                C158 v20 v21 v23 v24 v25 v26)
                                                             (addInt (coe (2 :: Integer)) (coe v0))
                                                             (addInt (coe (1 :: Integer)) (coe v0))
                                                             erased v13
                                                             (coe
                                                                (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                   C158 v20 v21 v23 v24 v25 v26)
                                                                v0
                                                                (addInt
                                                                   (coe (1 :: Integer)) (coe v0))
                                                                erased v2 v3 v14
                                                                (coe
                                                                   (\ v20 ->
                                                                      MAlonzo.Code.Data.AVL.Height.C32)
                                                                   erased))
                                                             v15
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.AVL.Height.C40)
                                                                erased)))
                                                MAlonzo.Code.Data.AVL.Height.C36
                                                  -> coe
                                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                          (coe
                                                             (\ v20 v21 ->
                                                                MAlonzo.Code.Data.Fin.Base.C16 v21)
                                                             erased
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.Fin.Base.C10)
                                                                erased))
                                                          (coe
                                                             (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                C158 v20 v21 v23 v24 v25 v26)
                                                             v0
                                                             (MAlonzo.Code.Data.AVL.Height.d14
                                                                (coe
                                                                   (\ v20 v21 ->
                                                                      MAlonzo.Code.Data.Fin.Base.C16
                                                                        v21)
                                                                   erased
                                                                   (coe
                                                                      (\ v20 ->
                                                                         MAlonzo.Code.Data.Fin.Base.C10)
                                                                      erased))
                                                                (coe v0))
                                                             erased v2 v3
                                                             (coe
                                                                (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                   C158 v20 v21 v23 v24 v25 v26)
                                                                v10 v11 erased v13 v14 v15
                                                                (coe
                                                                   (\ v20 ->
                                                                      MAlonzo.Code.Data.AVL.Height.C36)
                                                                   erased))
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.AVL.Height.C32)
                                                                erased)))
                                                MAlonzo.Code.Data.AVL.Height.C40
                                                  -> coe
                                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                          (coe
                                                             (\ v20 ->
                                                                MAlonzo.Code.Data.Fin.Base.C10)
                                                             erased)
                                                          (coe
                                                             (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                C158 v20 v21 v23 v24 v25 v26)
                                                             (addInt (coe (1 :: Integer)) (coe v1))
                                                             (MAlonzo.Code.Data.AVL.Height.d14
                                                                (coe
                                                                   (\ v20 v21 ->
                                                                      MAlonzo.Code.Data.Fin.Base.C16
                                                                        v21)
                                                                   erased
                                                                   (coe
                                                                      (\ v20 ->
                                                                         MAlonzo.Code.Data.Fin.Base.C10)
                                                                      erased))
                                                                (coe v1))
                                                             erased v2 v3
                                                             (coe
                                                                (\ v20 v21 v22 v23 v24 v25 v26 ->
                                                                   C158 v20 v21 v23 v24 v25 v26)
                                                                v10 v11 erased v13 v14 v15
                                                                (coe
                                                                   (\ v20 ->
                                                                      MAlonzo.Code.Data.AVL.Height.C36)
                                                                   erased))
                                                             (coe
                                                                (\ v20 ->
                                                                   MAlonzo.Code.Data.AVL.Height.C36)
                                                                erased)))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> coe v17 in
                               case coe v14 of
                                 C158 v18 v19 v21 v22 v23 v24
                                   -> case coe v16 of
                                        MAlonzo.Code.Data.AVL.Height.C40
                                          -> case coe v5 of
                                               MAlonzo.Code.Data.AVL.Height.C32
                                                 -> coe
                                                      (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                         (coe
                                                            (\ v27 ->
                                                               MAlonzo.Code.Data.Fin.Base.C10)
                                                            erased)
                                                         (coe
                                                            (\ v27 v28 v29 v30 v31 v32 v33 ->
                                                               C158 v27 v28 v30 v31 v32 v33)
                                                            (addInt (coe (1 :: Integer)) (coe v0))
                                                            (addInt (coe (1 :: Integer)) (coe v0))
                                                            erased v21
                                                            (coe
                                                               (\ v27 v28 v29 v30 v31 v32 v33 ->
                                                                  C158 v27 v28 v30 v31 v32 v33)
                                                               v0 v18 erased v2 v3 v22
                                                               (MAlonzo.Code.Data.AVL.Height.du48
                                                                  (coe v24)))
                                                            (coe
                                                               (\ v27 v28 v29 v30 v31 v32 v33 ->
                                                                  C158 v27 v28 v30 v31 v32 v33)
                                                               v19 v0 erased v13 v23 v15
                                                               (MAlonzo.Code.Data.AVL.Height.du56
                                                                  (coe v24)))
                                                            (coe
                                                               (\ v27 ->
                                                                  MAlonzo.Code.Data.AVL.Height.C36)
                                                               erased)))
                                               _ -> coe v17
                                        _ -> coe v17
                                 _ -> coe v17
                          _ -> case coe v5 of
                                 MAlonzo.Code.Data.AVL.Height.C36
                                   -> coe
                                        (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                           (coe
                                              (\ v11 v12 -> MAlonzo.Code.Data.Fin.Base.C16 v12)
                                              erased
                                              (coe
                                                 (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                           (coe
                                              (\ v11 v12 v13 v14 v15 v16 v17 ->
                                                 C158 v11 v12 v14 v15 v16 v17)
                                              v0
                                              (MAlonzo.Code.Data.AVL.Height.d14
                                                 (coe
                                                    (\ v11 v12 ->
                                                       MAlonzo.Code.Data.Fin.Base.C16 v12)
                                                    erased
                                                    (coe
                                                       (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10)
                                                       erased))
                                                 (coe v0))
                                              erased v2 v3 v7
                                              (coe
                                                 (\ v11 -> MAlonzo.Code.Data.AVL.Height.C32)
                                                 erased)))
                                 MAlonzo.Code.Data.AVL.Height.C40
                                   -> coe
                                        (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                           (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                           (coe
                                              (\ v11 v12 v13 v14 v15 v16 v17 ->
                                                 C158 v11 v12 v14 v15 v16 v17)
                                              (addInt (coe (1 :: Integer)) (coe v1))
                                              (MAlonzo.Code.Data.AVL.Height.d14
                                                 (coe
                                                    (\ v11 v12 ->
                                                       MAlonzo.Code.Data.Fin.Base.C16 v12)
                                                    erased
                                                    (coe
                                                       (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10)
                                                       erased))
                                                 (coe v1))
                                              erased v2 v3 v7
                                              (coe
                                                 (\ v11 -> MAlonzo.Code.Data.AVL.Height.C36)
                                                 erased)))
                                 _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name436 = "Data.AVL.Indexed._.joinˡ⁻"
d436 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  T130 ->
  MAlonzo.Code.Data.AVL.Height.T28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d436 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = du436 v8 v9 v11 v12 v13 v14
du436 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  T130 ->
  MAlonzo.Code.Data.AVL.Height.T28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du436 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      0 -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C32 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Data.Fin.Base.C10
                      -> coe
                           (MAlonzo.Code.Agda.Builtin.Sigma.C32
                              (coe
                                 (\ v9 v10 -> MAlonzo.Code.Data.Fin.Base.C16 v10) erased
                                 (coe (\ v9 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                              (coe
                                 (\ v9 v10 v11 v12 v13 v14 v15 -> C158 v9 v10 v12 v13 v14 v15)
                                 (MAlonzo.Code.Data.AVL.Height.d20
                                    (coe (\ v9 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                    (coe (0 :: Integer)))
                                 v1 erased v2 v7 v4 v5))
                    MAlonzo.Code.Data.Fin.Base.C16 v9
                      -> coe
                           (seq
                              (coe v9)
                              (coe
                                 (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                    (coe
                                       (\ v10 v11 -> MAlonzo.Code.Data.Fin.Base.C16 v11) erased
                                       (coe (\ v10 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                    (coe
                                       (\ v10 v11 v12 v13 v14 v15 v16 ->
                                          C158 v10 v11 v13 v14 v15 v16)
                                       (MAlonzo.Code.Data.AVL.Height.d20
                                          (coe
                                             (\ v10 v11 -> MAlonzo.Code.Data.Fin.Base.C16 v11)
                                             erased
                                             (coe (\ v10 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                          (coe (0 :: Integer)))
                                       v1 erased v2 v7 v4 v5))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v6 = subInt (coe v0) (coe (1 :: Integer)) in
           case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C32 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Data.Fin.Base.C10
                      -> case coe v5 of
                           MAlonzo.Code.Data.AVL.Height.C32
                             -> coe
                                  (du360
                                     (coe
                                        (MAlonzo.Code.Data.AVL.Height.d20
                                           (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                           (coe v0)))
                                     (coe v0) (coe v2) (coe v8)
                                     (coe
                                        (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                           (coe
                                              (\ v11 v12 -> MAlonzo.Code.Data.Fin.Base.C16 v12)
                                              erased
                                              (coe
                                                 (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                           (coe v4)))
                                     (coe (\ v11 -> MAlonzo.Code.Data.AVL.Height.C32) erased))
                           MAlonzo.Code.Data.AVL.Height.C36
                             -> coe
                                  (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                     (coe
                                        (\ v11 v12 -> MAlonzo.Code.Data.Fin.Base.C16 v12) erased
                                        (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                     (coe
                                        (\ v11 v12 v13 v14 v15 v16 v17 ->
                                           C158 v11 v12 v14 v15 v16 v17)
                                        (MAlonzo.Code.Data.AVL.Height.d20
                                           (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                           (coe v0))
                                        v0 erased v2 v8 v4
                                        (coe (\ v11 -> MAlonzo.Code.Data.AVL.Height.C32) erased)))
                           MAlonzo.Code.Data.AVL.Height.C40
                             -> coe
                                  (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                     (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                     (coe
                                        (\ v11 v12 v13 v14 v15 v16 v17 ->
                                           C158 v11 v12 v14 v15 v16 v17)
                                        (MAlonzo.Code.Data.AVL.Height.d20
                                           (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                           (coe v0))
                                        v6 erased v2 v8 v4
                                        (coe (\ v11 -> MAlonzo.Code.Data.AVL.Height.C36) erased)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Fin.Base.C16 v10
                      -> coe
                           (seq
                              (coe v10)
                              (coe
                                 (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                    (coe
                                       (\ v11 v12 -> MAlonzo.Code.Data.Fin.Base.C16 v12) erased
                                       (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                    (coe
                                       (\ v11 v12 v13 v14 v15 v16 v17 ->
                                          C158 v11 v12 v14 v15 v16 v17)
                                       (MAlonzo.Code.Data.AVL.Height.d20
                                          (coe
                                             (\ v11 v12 -> MAlonzo.Code.Data.Fin.Base.C16 v12)
                                             erased
                                             (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                          (coe v0))
                                       v1 erased v2 v8 v4 v5))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
name498 = "Data.AVL.Indexed._.joinʳ⁻"
d498 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  T130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Data.AVL.Height.T28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d498 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = du498 v8 v9 v11 v12 v13 v14
du498 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  T130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Data.AVL.Height.T28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du498 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      0 -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C32 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Data.Fin.Base.C10
                      -> coe
                           (MAlonzo.Code.Agda.Builtin.Sigma.C32
                              (coe
                                 (\ v9 v10 -> MAlonzo.Code.Data.Fin.Base.C16 v10) erased
                                 (coe (\ v9 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                              (coe
                                 (\ v9 v10 v11 v12 v13 v14 v15 -> C158 v9 v10 v12 v13 v14 v15) v0
                                 (MAlonzo.Code.Data.AVL.Height.d20
                                    (coe (\ v9 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                    (coe (0 :: Integer)))
                                 erased v2 v3 v7 v5))
                    MAlonzo.Code.Data.Fin.Base.C16 v9
                      -> coe
                           (seq
                              (coe v9)
                              (coe
                                 (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                    (coe
                                       (\ v10 v11 -> MAlonzo.Code.Data.Fin.Base.C16 v11) erased
                                       (coe (\ v10 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                    (coe
                                       (\ v10 v11 v12 v13 v14 v15 v16 ->
                                          C158 v10 v11 v13 v14 v15 v16)
                                       v0
                                       (MAlonzo.Code.Data.AVL.Height.d20
                                          (coe
                                             (\ v10 v11 -> MAlonzo.Code.Data.Fin.Base.C16 v11)
                                             erased
                                             (coe (\ v10 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                          (coe (0 :: Integer)))
                                       erased v2 v3 v7 v5))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
           case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C32 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Data.Fin.Base.C10
                      -> case coe v5 of
                           MAlonzo.Code.Data.AVL.Height.C32
                             -> coe
                                  (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                     (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                     (coe
                                        (\ v11 v12 v13 v14 v15 v16 v17 ->
                                           C158 v11 v12 v14 v15 v16 v17)
                                        v6
                                        (MAlonzo.Code.Data.AVL.Height.d20
                                           (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                           (coe v1))
                                        erased v2 v3 v8
                                        (coe (\ v11 -> MAlonzo.Code.Data.AVL.Height.C36) erased)))
                           MAlonzo.Code.Data.AVL.Height.C36
                             -> coe
                                  (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                     (coe
                                        (\ v11 v12 -> MAlonzo.Code.Data.Fin.Base.C16 v12) erased
                                        (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                     (coe
                                        (\ v11 v12 v13 v14 v15 v16 v17 ->
                                           C158 v11 v12 v14 v15 v16 v17)
                                        v1
                                        (MAlonzo.Code.Data.AVL.Height.d20
                                           (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                           (coe v1))
                                        erased v2 v3 v8
                                        (coe (\ v11 -> MAlonzo.Code.Data.AVL.Height.C40) erased)))
                           MAlonzo.Code.Data.AVL.Height.C40
                             -> coe
                                  (du284
                                     (coe v1)
                                     (coe
                                        (MAlonzo.Code.Data.AVL.Height.d20
                                           (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                           (coe v1)))
                                     (coe v2)
                                     (coe
                                        (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                           (coe
                                              (\ v11 v12 -> MAlonzo.Code.Data.Fin.Base.C16 v12)
                                              erased
                                              (coe
                                                 (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                           (coe v3)))
                                     (coe v8)
                                     (coe (\ v11 -> MAlonzo.Code.Data.AVL.Height.C40) erased))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Fin.Base.C16 v10
                      -> coe
                           (seq
                              (coe v10)
                              (coe
                                 (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                    (coe
                                       (\ v11 v12 -> MAlonzo.Code.Data.Fin.Base.C16 v12) erased
                                       (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                    (coe
                                       (\ v11 v12 v13 v14 v15 v16 v17 ->
                                          C158 v11 v12 v14 v15 v16 v17)
                                       v0
                                       (MAlonzo.Code.Data.AVL.Height.d20
                                          (coe
                                             (\ v11 v12 -> MAlonzo.Code.Data.Fin.Base.C16 v12)
                                             erased
                                             (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                                          (coe v1))
                                       erased v2 v3 v8 v5))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
name552 = "Data.AVL.Indexed._.headTail"
d552 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer -> T130 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d552 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du552 v9
du552 :: T130 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du552 v0
  = case coe v0 of
      C158 v1 v2 v4 v5 v6 v7
        -> let v8
                 = let v8 = du552 (coe v5) in
                   case coe v8 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C32 v9 v10
                       -> case coe v10 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C32 v11 v12
                              -> coe
                                   (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                      (coe v9)
                                      (coe
                                         (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                            (coe v11)
                                            (coe
                                               (du436
                                                  (coe v1) (coe v2) (coe v4) (coe v12) (coe v6)
                                                  (coe v7))))))
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError in
           case coe v5 of
             C142 v9
               -> case coe v7 of
                    MAlonzo.Code.Data.AVL.Height.C32
                      -> coe
                           (MAlonzo.Code.Agda.Builtin.Sigma.C32
                              (coe v4)
                              (coe
                                 (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                    (coe v9)
                                    (coe
                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                          (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                          (coe v6))))))
                    MAlonzo.Code.Data.AVL.Height.C36
                      -> coe
                           (MAlonzo.Code.Agda.Builtin.Sigma.C32
                              (coe v4)
                              (coe
                                 (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                    (coe v9)
                                    (coe
                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                          (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                          (coe v6))))))
                    _ -> coe v8
             _ -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
name602 = "Data.AVL.Indexed._.initLast"
d602 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer -> T130 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d602 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du602 v9
du602 :: T130 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du602 v0
  = case coe v0 of
      C158 v1 v2 v4 v5 v6 v7
        -> let v8
                 = let v8 = du602 (coe v6) in
                   case coe v8 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C32 v9 v10
                       -> case coe v10 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C32 v11 v12
                              -> coe
                                   (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                      (coe v9)
                                      (coe
                                         (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                            (coe v11)
                                            (coe
                                               (du498
                                                  (coe v1) (coe v2) (coe v4) (coe v5) (coe v12)
                                                  (coe v7))))))
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError in
           case coe v6 of
             C142 v9
               -> case coe v7 of
                    MAlonzo.Code.Data.AVL.Height.C36
                      -> coe
                           (MAlonzo.Code.Agda.Builtin.Sigma.C32
                              (coe v4)
                              (coe
                                 (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                    (coe v9)
                                    (coe
                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                          (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                          (coe v5))))))
                    MAlonzo.Code.Data.AVL.Height.C40
                      -> coe
                           (MAlonzo.Code.Agda.Builtin.Sigma.C32
                              (coe v4)
                              (coe
                                 (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                    (coe v9)
                                    (coe
                                       (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                          (coe (\ v11 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                          (coe v5))))))
                    _ -> coe v8
             _ -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
name658 = "Data.AVL.Indexed._.join"
d658 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer ->
  Integer ->
  Integer ->
  T130 ->
  T130 ->
  MAlonzo.Code.Data.AVL.Height.T28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d658 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = du658 v3 v6 v7 v8 v9 v10 v12 v13 v14
du658 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer ->
  Integer ->
  T130 ->
  T130 ->
  MAlonzo.Code.Data.AVL.Height.T28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du658 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = let v9
          = let v9 = du552 (coe v7) in
            case coe v9 of
              MAlonzo.Code.Agda.Builtin.Sigma.C32 v10 v11
                -> case coe v11 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C32 v12 v13
                       -> coe
                            (du498
                               (coe v4) (coe v5) (coe v10)
                               (coe
                                  (du248
                                     (coe v0) (coe v1) (coe v2)
                                     (coe
                                        (MAlonzo.Code.Data.Maybe.Base.C28
                                           (coe
                                              (MAlonzo.Code.Data.Maybe.Base.C28
                                                 (coe
                                                    (MAlonzo.Code.Agda.Builtin.Sigma.d28
                                                       (coe v10)))))))
                                     (coe v6) (coe v12)))
                               (coe v13) (coe v8))
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError in
    case coe v7 of
      C142 v10
        -> case coe v8 of
             MAlonzo.Code.Data.AVL.Height.C36
               -> coe
                    (MAlonzo.Code.Agda.Builtin.Sigma.C32
                       (coe (\ v12 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                       (coe
                          (du248 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v10))))
             MAlonzo.Code.Data.AVL.Height.C40
               -> coe
                    (MAlonzo.Code.Agda.Builtin.Sigma.C32
                       (coe (\ v12 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                       (coe
                          (du248 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v10))))
             _ -> coe v9
      _ -> coe v9
name694 = "Data.AVL.Indexed._.empty"
d694 ::
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  T130
d694 v0 v1 v2 = du694
du694 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T20 ->
  T130
du694 = coe C142
name702 = "Data.AVL.Indexed._.singleton"
d702 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14 -> T130
d702 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du702 v8 v9 v10
du702 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T14 -> T130
du702 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C32 v3 v4
        -> coe
             (\ v5 v6 v7 v8 v9 v10 v11 -> C158 v5 v6 v8 v9 v10 v11)
             (0 :: Integer) (0 :: Integer) erased
             (MAlonzo.Code.Agda.Builtin.Sigma.C32 (coe v0) (coe v1))
             (C142 (coe v3)) (C142 (coe v4))
             (coe (\ v5 -> MAlonzo.Code.Data.AVL.Height.C36) erased)
      _ -> MAlonzo.RTE.mazUnreachableError
name722 = "Data.AVL.Indexed._.insertWith"
d722 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer ->
  AgdaAny ->
  (MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) ->
  T130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d722 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = du722 v3 v5 v9 v10 v11 v12
du722 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  AgdaAny ->
  (MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) ->
  T130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du722 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C142 v6
        -> coe
             (MAlonzo.Code.Agda.Builtin.Sigma.C32
                (coe
                   (\ v7 v8 -> MAlonzo.Code.Data.Fin.Base.C16 v8) erased
                   (coe (\ v7 -> MAlonzo.Code.Data.Fin.Base.C10) erased))
                (coe
                   (du702
                      (coe v2) (coe v3 MAlonzo.Code.Data.Maybe.Base.C30) (coe v5))))
      C158 v6 v7 v9 v10 v11 v12
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C32 v13 v14
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C32 v15 v16
                      -> let v17
                               = coe
                                   MAlonzo.Code.Relation.Binary.d1226
                                   (MAlonzo.Code.Relation.Binary.d1290 (coe v0)) v2 v13 in
                         case coe v17 of
                           MAlonzo.Code.Relation.Binary.Core.C212 v18
                             -> coe
                                  (du284
                                     (coe v6) (coe v7) (coe v9)
                                     (coe
                                        (du722
                                           (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                                           (coe
                                              (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                 (coe v15)
                                                 (coe
                                                    (\ v21 v22 v23 ->
                                                       MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26
                                                         v23)
                                                    erased erased
                                                    (coe
                                                       (\ v21 v22 v23 ->
                                                          MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C30
                                                            v23)
                                                       erased erased v18))))))
                                     (coe v11) (coe v12))
                           MAlonzo.Code.Relation.Binary.Core.C220 v19
                             -> coe
                                  (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                     (coe (\ v21 -> MAlonzo.Code.Data.Fin.Base.C10) erased)
                                     (coe
                                        (\ v21 v22 v23 v24 v25 v26 v27 ->
                                           C158 v21 v22 v24 v25 v26 v27)
                                        v6 v7 erased
                                        (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                           (coe v13)
                                           (coe
                                              MAlonzo.Code.Data.AVL.Value.d46 v1 v2 v13 v19
                                              (coe
                                                 v3
                                                 (MAlonzo.Code.Data.Maybe.Base.C28
                                                    (coe
                                                       MAlonzo.Code.Data.AVL.Value.d46 v1 v13 v2
                                                       (coe
                                                          MAlonzo.Code.Relation.Binary.Core.d416
                                                          (MAlonzo.Code.Relation.Binary.d1222
                                                             (coe
                                                                (MAlonzo.Code.Relation.Binary.d1290
                                                                   (coe v0))))
                                                          v2 v13 v19)
                                                       v14)))))
                                        v10 v11 v12))
                           MAlonzo.Code.Relation.Binary.Core.C228 v20
                             -> coe
                                  (du360
                                     (coe v6) (coe v7) (coe v9) (coe v10)
                                     (coe
                                        (du722
                                           (coe v0) (coe v1) (coe v2) (coe v3) (coe v11)
                                           (coe
                                              (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                 (coe
                                                    (\ v21 v22 v23 ->
                                                       MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26
                                                         v23)
                                                    erased erased
                                                    (coe
                                                       (\ v21 v22 v23 ->
                                                          MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C30
                                                            v23)
                                                       erased erased v20))
                                                 (coe v16)))))
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name824 = "Data.AVL.Indexed._.insert"
d824 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  T130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d824 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du824 v3 v5 v9 v10
du824 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  AgdaAny ->
  AgdaAny ->
  T130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du824 v0 v1 v2 v3
  = coe (du722 (coe v0) (coe v1) (coe v2) (coe (\ v4 -> v3)))
name840 = "Data.AVL.Indexed._.delete"
d840 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer ->
  AgdaAny ->
  T130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
d840 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du840 v3 v6 v7 v9 v10 v11
du840 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  AgdaAny ->
  T130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14
du840 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C142 v6
        -> coe
             (MAlonzo.Code.Agda.Builtin.Sigma.C32
                (coe (\ v7 -> MAlonzo.Code.Data.Fin.Base.C10) erased) (coe v4))
      C158 v6 v7 v9 v10 v11 v12
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C32 v13 v14
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C32 v15 v16
                      -> let v17
                               = coe
                                   MAlonzo.Code.Relation.Binary.d1226
                                   (MAlonzo.Code.Relation.Binary.d1290 (coe v0)) v13 v3 in
                         case coe v17 of
                           MAlonzo.Code.Relation.Binary.Core.C212 v18
                             -> coe
                                  (du498
                                     (coe v6) (coe v7) (coe v9) (coe v10)
                                     (coe
                                        (du840
                                           (coe v0)
                                           (coe
                                              (MAlonzo.Code.Data.Maybe.Base.C28
                                                 (coe
                                                    (MAlonzo.Code.Data.Maybe.Base.C28 (coe v13)))))
                                           (coe v2) (coe v3) (coe v11)
                                           (coe
                                              (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                 (coe
                                                    (\ v21 v22 v23 ->
                                                       MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26
                                                         v23)
                                                    erased erased
                                                    (coe
                                                       (\ v21 v22 v23 ->
                                                          MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C30
                                                            v23)
                                                       erased erased v18))
                                                 (coe v16)))))
                                     (coe v12))
                           MAlonzo.Code.Relation.Binary.Core.C220 v19
                             -> coe
                                  (du658
                                     (coe v0) (coe v1)
                                     (coe
                                        (MAlonzo.Code.Data.Maybe.Base.C28
                                           (coe (MAlonzo.Code.Data.Maybe.Base.C28 (coe v13)))))
                                     (coe v2) (coe v6) (coe v7) (coe v10) (coe v11) (coe v12))
                           MAlonzo.Code.Relation.Binary.Core.C228 v20
                             -> coe
                                  (du436
                                     (coe v6) (coe v7) (coe v9)
                                     (coe
                                        (du840
                                           (coe v0) (coe v1)
                                           (coe
                                              (MAlonzo.Code.Data.Maybe.Base.C28
                                                 (coe
                                                    (MAlonzo.Code.Data.Maybe.Base.C28 (coe v13)))))
                                           (coe v3) (coe v10)
                                           (coe
                                              (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                 (coe v15)
                                                 (coe
                                                    (\ v21 v22 v23 ->
                                                       MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26
                                                         v23)
                                                    erased erased
                                                    (coe
                                                       (\ v21 v22 v23 ->
                                                          MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C30
                                                            v23)
                                                       erased erased v20))))))
                                     (coe v11) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name938 = "Data.AVL.Indexed._.lookup"
d938 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer ->
  AgdaAny ->
  T130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Data.Maybe.Base.T22
d938 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 = du938 v3 v5 v9 v10 v11
du938 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  AgdaAny ->
  T130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 ->
  MAlonzo.Code.Data.Maybe.Base.T22
du938 v0 v1 v2 v3 v4
  = case coe v3 of
      C142 v5 -> coe MAlonzo.Code.Data.Maybe.Base.C30
      C158 v5 v6 v8 v9 v10 v11
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C32 v12 v13
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C32 v14 v15
                      -> let v16
                               = coe
                                   MAlonzo.Code.Relation.Binary.d1226
                                   (MAlonzo.Code.Relation.Binary.d1290 (coe v0)) v12 v2 in
                         case coe v16 of
                           MAlonzo.Code.Relation.Binary.Core.C212 v17
                             -> coe
                                  (du938
                                     (coe v0) (coe v1) (coe v2) (coe v10)
                                     (coe
                                        (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                           (coe
                                              (\ v20 v21 v22 ->
                                                 MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26
                                                   v22)
                                              erased erased
                                              (coe
                                                 (\ v20 v21 v22 ->
                                                    MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C30
                                                      v22)
                                                 erased erased v17))
                                           (coe v15))))
                           MAlonzo.Code.Relation.Binary.Core.C220 v18
                             -> coe
                                  (MAlonzo.Code.Data.Maybe.Base.C28
                                     (coe MAlonzo.Code.Data.AVL.Value.d46 v1 v12 v2 v18 v13))
                           MAlonzo.Code.Relation.Binary.Core.C228 v19
                             -> coe
                                  (du938
                                     (coe v0) (coe v1) (coe v2) (coe v9)
                                     (coe
                                        (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                           (coe v14)
                                           (coe
                                              (\ v20 v21 v22 ->
                                                 MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26
                                                   v22)
                                              erased erased
                                              (coe
                                                 (\ v20 v21 v22 ->
                                                    MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C30
                                                      v22)
                                                 erased erased v19)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name1016 = "Data.AVL.Indexed._.toDiffList"
d1016 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer ->
  T130 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T14]
d1016 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du1016 v9
du1016 ::
  T130 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T14]
du1016 v0
  = case coe v0 of
      C142 v1 -> coe (\ v2 -> v2)
      C158 v1 v2 v4 v5 v6 v7
        -> coe
             (\ v8 ->
                coe
                  du1016 v5
                  (MAlonzo.Code.Agda.Builtin.List.C22 (coe v4) (coe du1016 v6 v8)))
      _ -> MAlonzo.RTE.mazUnreachableError
name1030 = "Data.AVL.Indexed._.toList"
d1030 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  Integer -> T130 -> [MAlonzo.Code.Agda.Builtin.Sigma.T14]
d1030 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du1030 v9
du1030 :: T130 -> [MAlonzo.Code.Agda.Builtin.Sigma.T14]
du1030 v0 = coe du1016 v0 MAlonzo.Code.Agda.Builtin.List.C16
name1046 = "Data.AVL.Indexed._.Val"
d1046 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> ()
d1046 = erased
name1048 = "Data.AVL.Indexed._.Wal"
d1048 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> ()
d1048 = erased
name1056 = "Data.AVL.Indexed._.map"
d1056 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Maybe.Base.T22 ->
  MAlonzo.Code.Data.Maybe.Base.T22 -> Integer -> T130 -> T130
d1056 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 = du1056 v8 v12
du1056 :: (AgdaAny -> AgdaAny -> AgdaAny) -> T130 -> T130
du1056 v0 v1
  = case coe v1 of
      C142 v2 -> coe v1
      C158 v2 v3 v5 v6 v7 v8
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C32 v9 v10
               -> coe
                    (\ v11 v12 v13 v14 v15 v16 v17 -> C158 v11 v12 v14 v15 v16 v17) v2
                    v3 erased
                    (MAlonzo.Code.Agda.Builtin.Sigma.C32 (coe v9) (coe v0 v9 v10))
                    (du1056 (coe v0) (coe v6)) (du1056 (coe v0) (coe v7)) v8
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
