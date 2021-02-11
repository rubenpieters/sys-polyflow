{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Alg where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Relation.Nullary

name38 = "Alg.Id"
d38 :: ()
d38 = erased
name40 = "Alg.Label"
d40 :: ()
d40 = erased
name42 = "Alg.Obj"
d42 = ()
data T42 = C46 | C48 MAlonzo.Code.Agda.Builtin.String.T6 T44 T42
name44 = "Alg.Type"
d44 = ()
data T44
  = C50 | C52 | C54 MAlonzo.Code.Agda.Builtin.String.T6 | C56 T42 |
    C58 T44 T44 | C60 T44 T44
name62 = "Alg.e1"
d62 :: T44
d62
  = coe
      (C58
         (coe
            (C56
               (coe
                  (C48
                     (coe (Data.Text.pack "t")) (coe C50)
                     (coe (C48 (coe (Data.Text.pack "f")) (coe C52) (coe C46)))))))
         (coe (C54 (coe (Data.Text.pack "t")))))
name64 = "Alg._<canindex>_"
d64 a0 a1 = ()
data T64 = C72 | C82 T64
name88 = "Alg.canIndex"
d88 :: T44 -> T42 -> MAlonzo.Code.Relation.Nullary.T14
d88 v0 v1
  = case coe v0 of
      C50 -> coe (\ v2 -> MAlonzo.Code.Relation.Nullary.C26) erased
      C52 -> coe (\ v2 -> MAlonzo.Code.Relation.Nullary.C26) erased
      C54 v2
        -> case coe v1 of
             C46 -> coe (\ v3 -> MAlonzo.Code.Relation.Nullary.C26) erased
             C48 v3 v4 v5
               -> let v6
                        = MAlonzo.Code.Data.String.Properties.d64 (coe v2) (coe v3) in
                  case coe v6 of
                    MAlonzo.Code.Relation.Nullary.C22 v7
                      -> coe
                           (MAlonzo.Code.Relation.Nullary.C22
                              (coe (\ v8 v9 v10 -> C72) erased erased erased))
                    MAlonzo.Code.Relation.Nullary.C26
                      -> let v8 = d88 (coe v0) (coe v5) in
                         case coe v8 of
                           MAlonzo.Code.Relation.Nullary.C22 v9
                             -> coe
                                  (MAlonzo.Code.Relation.Nullary.C22
                                     (coe
                                        (\ v10 v11 v12 v13 v14 v15 -> C82 v15) erased erased erased
                                        erased erased v9))
                           MAlonzo.Code.Relation.Nullary.C26
                             -> coe (\ v10 -> MAlonzo.Code.Relation.Nullary.C26) erased
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C56 v2 -> coe (\ v3 -> MAlonzo.Code.Relation.Nullary.C26) erased
      C58 v2 v3 -> coe (\ v4 -> MAlonzo.Code.Relation.Nullary.C26) erased
      C60 v2 v3 -> coe (\ v4 -> MAlonzo.Code.Relation.Nullary.C26) erased
      _ -> MAlonzo.RTE.mazUnreachableError
name168 = "Alg.safeLookup"
d168 :: T44 -> T42 -> T64 -> T44
d168 v0 v1 v2
  = coe
      (seq
         (coe v0)
         (case coe v1 of
            C48 v3 v4 v5
              -> case coe v2 of
                   C72 -> coe v4
                   C82 v11 -> coe (d168 (coe v0) (coe v5) (coe v11))
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
name178 = "Alg.Context"
d178 = ()
data T178 = C180
name182 = "Alg._⊢_<:_"
d182 a0 a1 a2 = ()
data T182 = C188
name190 = "Alg._⊢_⇝_"
d190 a0 a1 a2 = ()
data T190 = C204 T42 T44 T182 T182 T64
name206 = "Alg.imp"
d206 = error "MAlonzo Runtime Error: postulate evaluated: Alg.imp"
name214 = "Alg.simplify"
d214 :: T178 -> T44 -> MAlonzo.Code.Relation.Nullary.T14
d214 v0 v1 = du214 v1
du214 :: T44 -> MAlonzo.Code.Relation.Nullary.T14
du214 v0
  = case coe v0 of
      C50 -> coe (\ v1 -> MAlonzo.Code.Relation.Nullary.C26) erased
      C52 -> coe (\ v1 -> MAlonzo.Code.Relation.Nullary.C26) erased
      C54 v1 -> coe (\ v2 -> MAlonzo.Code.Relation.Nullary.C26) erased
      C56 v1 -> coe (\ v2 -> MAlonzo.Code.Relation.Nullary.C26) erased
      C58 v1 v2
        -> case coe v1 of
             C50 -> coe MAlonzo.Code.Data.Empty.d10 () erased erased
             C52 -> coe MAlonzo.Code.Data.Empty.d10 () erased erased
             C54 v3 -> coe MAlonzo.Code.Data.Empty.d10 () erased erased
             C56 v3
               -> let v4 = d88 (coe v2) (coe v3) in
                  case coe v4 of
                    MAlonzo.Code.Relation.Nullary.C22 v5
                      -> coe
                           (MAlonzo.Code.Relation.Nullary.C22
                              (coe
                                 (MAlonzo.Code.Agda.Builtin.Sigma.C32
                                    (coe (d168 (coe v2) (coe v3) (coe v5)))
                                    (coe
                                       (\ v6 v7 v8 v9 v10 v11 v12 v13 -> C204 v9 v10 v11 v12 v13)
                                       erased erased erased v3 v2
                                       (coe (\ v6 v7 -> C188) erased erased)
                                       (coe (\ v6 v7 -> C188) erased erased) v5))))
                    MAlonzo.Code.Relation.Nullary.C26
                      -> coe MAlonzo.Code.Data.Empty.d10 () erased erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             C58 v3 v4 -> coe MAlonzo.Code.Data.Empty.d10 () erased erased
             C60 v3 v4 -> coe MAlonzo.Code.Data.Empty.d10 () erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      C60 v1 v2 -> coe (\ v3 -> MAlonzo.Code.Relation.Nullary.C26) erased
      _ -> MAlonzo.RTE.mazUnreachableError
name290 = "Alg.test"
d290 :: MAlonzo.Code.Relation.Nullary.T14
d290 = coe (du214 (coe d62))
name411 = "Alg..absurdlambda"
d411 :: T42 -> T64 -> MAlonzo.Code.Data.Empty.T4
d411 = erased
name561 = "Alg..absurdlambda"
d561 :: T42 -> T64 -> MAlonzo.Code.Data.Empty.T4
d561 = erased
name645 = "Alg..absurdlambda"
d645 ::
  MAlonzo.Code.Agda.Builtin.String.T6 ->
  T64 -> MAlonzo.Code.Data.Empty.T4
d645 = erased
name3627 = "Alg..absurdlambda"
d3627 :: T42 -> T42 -> T64 -> MAlonzo.Code.Data.Empty.T4
d3627 = erased
name3849 = "Alg..absurdlambda"
d3849 :: T44 -> T44 -> T42 -> T64 -> MAlonzo.Code.Data.Empty.T4
d3849 = erased
name4071 = "Alg..absurdlambda"
d4071 :: T44 -> T44 -> T42 -> T64 -> MAlonzo.Code.Data.Empty.T4
d4071 = erased
name8231 = "Alg..absurdlambda"
d8231 ::
  T178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> MAlonzo.Code.Data.Empty.T4
d8231 = erased
name8383 = "Alg..absurdlambda"
d8383 ::
  T178 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> MAlonzo.Code.Data.Empty.T4
d8383 = erased
name8561 = "Alg..absurdlambda"
d8561 ::
  T178 ->
  MAlonzo.Code.Agda.Builtin.String.T6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> MAlonzo.Code.Data.Empty.T4
d8561 = erased
name8739 = "Alg..absurdlambda"
d8739 ::
  T178 ->
  T42 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> MAlonzo.Code.Data.Empty.T4
d8739 = erased
name9509 = "Alg..absurdlambda"
d9509 ::
  T178 ->
  T44 ->
  T44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T14 -> MAlonzo.Code.Data.Empty.T4
d9509 = erased
