{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.AVL where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.AVL.Height
import qualified MAlonzo.Code.Data.AVL.Indexed
import qualified MAlonzo.Code.Data.AVL.Value
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Product
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict

name80 = "Data.AVL.Indexed.K&_"
d80 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> ()
d80 = erased
name86 = "Data.AVL.Indexed.Tree"
d86 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
name88 = "Data.AVL.Indexed.Value"
d88 a0 a1 a2 a3 a4 = ()
name94 = "Data.AVL.Indexed.const"
d94 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Data.AVL.Value.T36
d94 v0 v1 v2 v3 = du94
du94 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Data.AVL.Value.T36
du94 = coe (\ v0 v1 -> MAlonzo.Code.Data.AVL.Value.du52)
name154 = "Data.AVL.Indexed.Value.family"
d154 :: MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> ()
d154 = erased
name156 = "Data.AVL.Indexed.Value.respects"
d156 ::
  MAlonzo.Code.Data.AVL.Value.T36 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d156 = coe MAlonzo.Code.Data.AVL.Value.d46
name194 = "Data.AVL.Tree"
d194 a0 a1 a2 a3 a4 a5 = ()
data T194 = C202 Integer MAlonzo.Code.Data.AVL.Indexed.T130
name212 = "Data.AVL._.Val"
d212 :: MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> ()
d212 = erased
name214 = "Data.AVL._.empty"
d214 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> T194
d214 v0 v1 v2 v3 v4 v5 = du214
du214 :: T194
du214
  = coe
      (C202
         (coe (0 :: Integer))
         (coe
            (MAlonzo.Code.Data.AVL.Indexed.C142
               (coe
                  (\ v0 ->
                     MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
                  erased))))
name218 = "Data.AVL._.singleton"
d218 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> AgdaAny -> T194
d218 v0 v1 v2 v3 v4 v5 v6 v7 = du218 v6 v7
du218 :: AgdaAny -> AgdaAny -> T194
du218 v0 v1
  = coe
      (C202
         (coe (1 :: Integer))
         (coe
            (MAlonzo.Code.Data.AVL.Indexed.du702
               (coe v0) (coe v1)
               (coe
                  (MAlonzo.Code.Agda.Builtin.Sigma.C32
                     (coe
                        (\ v2 v3 v4 ->
                           MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26 v4)
                        erased erased
                        (coe
                           (\ v2 ->
                              MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C24)
                           erased))
                     (coe
                        (\ v2 ->
                           MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
                        erased))))))
name226 = "Data.AVL._.insert"
d226 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  AgdaAny -> AgdaAny -> T194 -> T194
d226 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du226 v3 v5 v6 v7 v8
du226 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  AgdaAny -> AgdaAny -> T194 -> T194
du226 v0 v1 v2 v3 v4
  = case coe v4 of
      C202 v5 v6
        -> coe
             (C202
                (coe
                   (MAlonzo.Code.Data.AVL.Height.d14
                      (coe
                         (MAlonzo.Code.Agda.Builtin.Sigma.d28
                            (coe
                               MAlonzo.Code.Data.AVL.Indexed.du824 v0 v1 v2 v3 v6
                               (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                  (coe
                                     (\ v7 v8 v9 ->
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26
                                          v9)
                                     erased erased
                                     (coe
                                        (\ v7 ->
                                           MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C24)
                                        erased))
                                  (coe
                                     (\ v7 ->
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
                                     erased)))))
                      (coe v5)))
                (coe
                   (MAlonzo.Code.Agda.Builtin.Sigma.d30
                      (coe
                         MAlonzo.Code.Data.AVL.Indexed.du824 v0 v1 v2 v3 v6
                         (MAlonzo.Code.Agda.Builtin.Sigma.C32
                            (coe
                               (\ v7 v8 v9 ->
                                  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26 v9)
                               erased erased
                               (coe
                                  (\ v7 ->
                                     MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C24)
                                  erased))
                            (coe
                               (\ v7 ->
                                  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
                               erased))))))
      _ -> MAlonzo.RTE.mazUnreachableError
name236 = "Data.AVL._.insertWith"
d236 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  AgdaAny ->
  (MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) -> T194 -> T194
d236 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du236 v3 v5 v6 v7 v8
du236 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  AgdaAny ->
  (MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) -> T194 -> T194
du236 v0 v1 v2 v3 v4
  = case coe v4 of
      C202 v5 v6
        -> coe
             (C202
                (coe
                   (MAlonzo.Code.Data.AVL.Height.d14
                      (coe
                         (MAlonzo.Code.Agda.Builtin.Sigma.d28
                            (coe
                               (MAlonzo.Code.Data.AVL.Indexed.du722
                                  (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)
                                  (coe
                                     (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                        (coe
                                           (\ v7 v8 v9 ->
                                              MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26
                                                v9)
                                           erased erased
                                           (coe
                                              (\ v7 ->
                                                 MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C24)
                                              erased))
                                        (coe
                                           (\ v7 ->
                                              MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
                                           erased)))))))
                      (coe v5)))
                (coe
                   (MAlonzo.Code.Agda.Builtin.Sigma.d30
                      (coe
                         (MAlonzo.Code.Data.AVL.Indexed.du722
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)
                            (coe
                               (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                  (coe
                                     (\ v7 v8 v9 ->
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26
                                          v9)
                                     erased erased
                                     (coe
                                        (\ v7 ->
                                           MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C24)
                                        erased))
                                  (coe
                                     (\ v7 ->
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
                                     erased))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
name244 = "Data.AVL._.delete"
d244 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> T194 -> T194
d244 v0 v1 v2 v3 v4 v5 v6 v7 = du244 v3 v6 v7
du244 ::
  MAlonzo.Code.Relation.Binary.T1268 -> AgdaAny -> T194 -> T194
du244 v0 v1 v2
  = case coe v2 of
      C202 v3 v4
        -> coe
             (C202
                (coe
                   (MAlonzo.Code.Data.AVL.Height.d20
                      (coe
                         (MAlonzo.Code.Agda.Builtin.Sigma.d28
                            (coe
                               (MAlonzo.Code.Data.AVL.Indexed.du840
                                  (coe v0)
                                  (coe
                                     (MAlonzo.Code.Data.Maybe.Base.C28
                                        (coe MAlonzo.Code.Data.Maybe.Base.C30)))
                                  (coe MAlonzo.Code.Data.Maybe.Base.C30) (coe v1) (coe v4)
                                  (coe
                                     (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                        (coe
                                           (\ v5 v6 v7 ->
                                              MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26
                                                v7)
                                           erased erased
                                           (coe
                                              (\ v5 ->
                                                 MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C24)
                                              erased))
                                        (coe
                                           (\ v5 ->
                                              MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
                                           erased)))))))
                      (coe v3)))
                (coe
                   (MAlonzo.Code.Agda.Builtin.Sigma.d30
                      (coe
                         (MAlonzo.Code.Data.AVL.Indexed.du840
                            (coe v0)
                            (coe
                               (MAlonzo.Code.Data.Maybe.Base.C28
                                  (coe MAlonzo.Code.Data.Maybe.Base.C30)))
                            (coe MAlonzo.Code.Data.Maybe.Base.C30) (coe v1) (coe v4)
                            (coe
                               (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                  (coe
                                     (\ v5 v6 v7 ->
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26
                                          v7)
                                     erased erased
                                     (coe
                                        (\ v5 ->
                                           MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C24)
                                        erased))
                                  (coe
                                     (\ v5 ->
                                        MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
                                     erased))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
name252 = "Data.AVL._.lookup"
d252 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  AgdaAny -> T194 -> MAlonzo.Code.Data.Maybe.Base.T22
d252 v0 v1 v2 v3 v4 v5 v6 v7 = du252 v3 v5 v6 v7
du252 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  AgdaAny -> T194 -> MAlonzo.Code.Data.Maybe.Base.T22
du252 v0 v1 v2 v3
  = case coe v3 of
      C202 v4 v5
        -> coe
             (MAlonzo.Code.Data.AVL.Indexed.du938
                (coe v0) (coe v1) (coe v2) (coe v5)
                (coe
                   (MAlonzo.Code.Agda.Builtin.Sigma.C32
                      (coe
                         (\ v6 v7 v8 ->
                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26 v8)
                         erased erased
                         (coe
                            (\ v6 ->
                               MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C24)
                            erased))
                      (coe
                         (\ v6 ->
                            MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
                         erased))))
      _ -> MAlonzo.RTE.mazUnreachableError
name270 = "Data.AVL._.Val"
d270 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> ()
d270 = erased
name272 = "Data.AVL._.Wal"
d272 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> ()
d272 = erased
name274 = "Data.AVL._.map"
d274 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T194 -> T194
d274 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du274 v8 v9
du274 :: (AgdaAny -> AgdaAny -> AgdaAny) -> T194 -> T194
du274 v0 v1
  = case coe v1 of
      C202 v2 v3
        -> coe
             (C202
                (coe v2)
                (coe (MAlonzo.Code.Data.AVL.Indexed.du1056 (coe v0) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
name290 = "Data.AVL._._∈?_"
d290 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> T194 -> Bool
d290 v0 v1 v2 v3 v4 v5 v6 v7 = du290 v3 v5 v6 v7
du290 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> T194 -> Bool
du290 v0 v1 v2 v3
  = coe
      (MAlonzo.Code.Data.Maybe.Base.du34
         (coe (du252 (coe v0) (coe v1) (coe v2) (coe v3))))
name296 = "Data.AVL._.headTail"
d296 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  T194 -> MAlonzo.Code.Data.Maybe.Base.T22
d296 v0 v1 v2 v3 v4 v5 v6 = du296 v3 v6
du296 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  T194 -> MAlonzo.Code.Data.Maybe.Base.T22
du296 v0 v1
  = case coe v1 of
      C202 v2 v3
        -> let v4
                 = let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                   let v5 = MAlonzo.Code.Data.AVL.Indexed.du552 (coe v3) in
                   case coe v5 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C32 v6 v7
                       -> case coe v7 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C32 v8 v9
                              -> case coe v9 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C32 v10 v11
                                     -> coe
                                          (MAlonzo.Code.Data.Maybe.Base.C28
                                             (coe
                                                (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                   (coe v6)
                                                   (coe
                                                      (C202
                                                         (coe
                                                            (MAlonzo.Code.Data.AVL.Height.d14
                                                               (coe v10) (coe v4)))
                                                         (coe
                                                            (MAlonzo.Code.Data.AVL.Indexed.du222
                                                               (coe v0)
                                                               (coe
                                                                  (MAlonzo.Code.Data.Maybe.Base.C28
                                                                     (coe
                                                                        MAlonzo.Code.Data.Maybe.Base.C30)))
                                                               (coe
                                                                  (MAlonzo.Code.Data.Maybe.Base.C28
                                                                     (coe
                                                                        (MAlonzo.Code.Data.Maybe.Base.C28
                                                                           (coe
                                                                              (MAlonzo.Code.Agda.Builtin.Sigma.d28
                                                                                 (coe v6)))))))
                                                               (coe
                                                                  MAlonzo.Code.Data.Maybe.Base.C30)
                                                               (coe
                                                                  (\ v12 v13 v14 ->
                                                                     MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C26
                                                                       v14)
                                                                  erased erased
                                                                  (coe
                                                                     (\ v12 ->
                                                                        MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C24)
                                                                     erased))
                                                               (coe v11))))))))
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError in
           case coe v3 of
             MAlonzo.Code.Data.AVL.Indexed.C142 v5
               -> coe MAlonzo.Code.Data.Maybe.Base.C30
             _ -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
name310 = "Data.AVL._.initLast"
d310 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  T194 -> MAlonzo.Code.Data.Maybe.Base.T22
d310 v0 v1 v2 v3 v4 v5 v6 = du310 v3 v6
du310 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  T194 -> MAlonzo.Code.Data.Maybe.Base.T22
du310 v0 v1
  = case coe v1 of
      C202 v2 v3
        -> let v4
                 = let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                   let v5 = MAlonzo.Code.Data.AVL.Indexed.du602 (coe v3) in
                   case coe v5 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C32 v6 v7
                       -> case coe v7 of
                            MAlonzo.Code.Agda.Builtin.Sigma.C32 v8 v9
                              -> case coe v9 of
                                   MAlonzo.Code.Agda.Builtin.Sigma.C32 v10 v11
                                     -> coe
                                          (MAlonzo.Code.Data.Maybe.Base.C28
                                             (coe
                                                (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                                   (coe
                                                      (C202
                                                         (coe
                                                            (MAlonzo.Code.Data.AVL.Height.d14
                                                               (coe v10) (coe v4)))
                                                         (coe
                                                            (MAlonzo.Code.Data.AVL.Indexed.du248
                                                               (coe v0)
                                                               (coe
                                                                  (MAlonzo.Code.Data.Maybe.Base.C28
                                                                     (coe
                                                                        MAlonzo.Code.Data.Maybe.Base.C30)))
                                                               (coe
                                                                  (MAlonzo.Code.Data.Maybe.Base.C28
                                                                     (coe
                                                                        (MAlonzo.Code.Data.Maybe.Base.C28
                                                                           (coe
                                                                              (MAlonzo.Code.Agda.Builtin.Sigma.d28
                                                                                 (coe v6)))))))
                                                               (coe
                                                                  MAlonzo.Code.Data.Maybe.Base.C30)
                                                               (coe v11)
                                                               (coe
                                                                  (\ v12 ->
                                                                     MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
                                                                  erased)))))
                                                   (coe v6))))
                                   _ -> MAlonzo.RTE.mazUnreachableError
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError in
           case coe v3 of
             MAlonzo.Code.Data.AVL.Indexed.C142 v5
               -> coe MAlonzo.Code.Data.Maybe.Base.C30
             _ -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
name324 = "Data.AVL._.fromList"
d324 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T14] -> T194
d324 v0 v1 v2 v3 v4 v5 = du324 v3 v5
du324 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T14] -> T194
du324 v0 v1
  = coe
      (MAlonzo.Code.Data.List.Base.du202
         (coe
            (MAlonzo.Code.Data.Product.du234 (coe (du226 (coe v0) (coe v1)))))
         (coe
            (C202
               (coe (0 :: Integer))
               (coe
                  (MAlonzo.Code.Data.AVL.Indexed.C142
                     (coe
                        (\ v2 ->
                           MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
                        erased))))))
name326 = "Data.AVL._.toList"
d326 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  T194 -> [MAlonzo.Code.Agda.Builtin.Sigma.T14]
d326 v0 v1 v2 v3 v4 v5 v6 = du326 v6
du326 :: T194 -> [MAlonzo.Code.Agda.Builtin.Sigma.T14]
du326 v0
  = case coe v0 of
      C202 v1 v2
        -> coe
             MAlonzo.Code.Data.AVL.Indexed.du1016 v2
             MAlonzo.Code.Agda.Builtin.List.C16
      _ -> MAlonzo.RTE.mazUnreachableError
name342 = "Data.AVL._.Val"
d342 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> ()
d342 = erased
name344 = "Data.AVL._.Wal"
d344 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> ()
d344 = erased
name348 = "Data.AVL._.unionWith"
d348 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) ->
  T194 -> T194 -> T194
d348 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du348 v3 v7 v8 v9 v10
du348 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) ->
  T194 -> T194 -> T194
du348 v0 v1 v2 v3 v4
  = coe
      (MAlonzo.Code.Data.List.Base.du202
         (coe
            (MAlonzo.Code.Data.Product.du234
               (coe
                  (\ v5 v6 -> du236 (coe v0) (coe v1) (coe v5) (coe v2 v5 v6)))))
         (coe v4) (coe (du326 (coe v3))))
name368 = "Data.AVL._.Val"
d368 :: MAlonzo.Code.Data.AVL.Value.T36 -> AgdaAny -> ()
d368 = erased
name370 = "Data.AVL._.union"
d370 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> T194 -> T194 -> T194
d370 v0 v1 v2 v3 v4 v5 = du370 v3 v5
du370 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> T194 -> T194 -> T194
du370 v0 v1
  = coe (du348 (coe v0) (coe v1) (coe (\ v2 v3 v4 -> v3)))
name374 = "Data.AVL._.unionsWith"
d374 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) ->
  [T194] -> T194
d374 v0 v1 v2 v3 v4 v5 v6 v7 = du374 v3 v5 v6 v7
du374 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.Value.T36 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) ->
  [T194] -> T194
du374 v0 v1 v2 v3
  = coe
      (MAlonzo.Code.Data.List.Base.du202
         (coe (du348 (coe v0) (coe v1) (coe v2)))
         (coe
            (C202
               (coe (0 :: Integer))
               (coe
                  (MAlonzo.Code.Data.AVL.Indexed.C142
                     (coe
                        (\ v4 ->
                           MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
                        erased)))))
         (coe v3))
name380 = "Data.AVL._.unions"
d380 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> [T194] -> T194
d380 v0 v1 v2 v3 v4 v5 = du380 v3 v5
du380 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.Value.T36 -> [T194] -> T194
du380 v0 v1
  = coe (du374 (coe v0) (coe v1) (coe (\ v2 v3 v4 -> v3)))
