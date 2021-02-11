{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Map where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.AVL
import qualified MAlonzo.Code.Data.AVL.Indexed
import qualified MAlonzo.Code.Data.AVL.Value
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict

name16 = "Map.AVL.Tree"
d16 a0 a1 a2 a3 a4 a5 = ()
name132 = "Map.Map"
d132 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 -> () -> ()
d132 = erased
name144 = "Map._.empty"
d144 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 -> () -> MAlonzo.Code.Data.AVL.T194
d144 v0 v1 v2 v3 v4 v5 = du144
du144 :: MAlonzo.Code.Data.AVL.T194
du144
  = coe
      (MAlonzo.Code.Data.AVL.C202
         (coe (0 :: Integer))
         (coe
            (MAlonzo.Code.Data.AVL.Indexed.C142
               (coe
                  (\ v0 ->
                     MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C30)
                  erased))))
name146 = "Map._.singleton"
d146 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.AVL.T194
d146 v0 v1 v2 v3 v4 v5 = du146
du146 :: AgdaAny -> AgdaAny -> MAlonzo.Code.Data.AVL.T194
du146 = coe MAlonzo.Code.Data.AVL.du218
name148 = "Map._.insert"
d148 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.AVL.T194
d148 v0 v1 v2 v3 v4 v5 = du148 v3
du148 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.AVL.T194
du148 v0
  = coe
      (MAlonzo.Code.Data.AVL.du226
         (coe v0)
         (coe
            (\ v1 v2 -> MAlonzo.Code.Data.AVL.Value.C48 v2) erased
            (\ v1 v2 v3 v4 -> v4)))
name150 = "Map._.insertWith"
d150 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.AVL.T194
d150 v0 v1 v2 v3 v4 v5 = du150 v3
du150 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  AgdaAny ->
  (MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.AVL.T194
du150 v0
  = coe
      (MAlonzo.Code.Data.AVL.du236
         (coe v0)
         (coe
            (\ v1 v2 -> MAlonzo.Code.Data.AVL.Value.C48 v2) erased
            (\ v1 v2 v3 v4 -> v4)))
name152 = "Map._.delete"
d152 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny -> MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.AVL.T194
d152 v0 v1 v2 v3 v4 v5 = du152 v3
du152 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  AgdaAny -> MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.AVL.T194
du152 v0 = coe (MAlonzo.Code.Data.AVL.du244 (coe v0))
name154 = "Map._.lookup"
d154 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.Maybe.Base.T22
d154 v0 v1 v2 v3 v4 v5 = du154 v3
du154 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  AgdaAny ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.Maybe.Base.T22
du154 v0
  = coe
      (MAlonzo.Code.Data.AVL.du252
         (coe v0) (coe MAlonzo.Code.Data.AVL.Value.du52))
name168 = "Map._.map"
d168 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.AVL.T194
d168 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du168 v8
du168 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.AVL.T194
du168 v0 = coe (MAlonzo.Code.Data.AVL.du274 (coe (\ v1 -> v0)))
name180 = "Map._._∈?_"
d180 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> AgdaAny -> MAlonzo.Code.Data.AVL.T194 -> Bool
d180 v0 v1 v2 v3 v4 v5 = du180 v3
du180 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  AgdaAny -> MAlonzo.Code.Data.AVL.T194 -> Bool
du180 v0
  = coe
      (MAlonzo.Code.Data.AVL.du290
         (coe v0) (coe MAlonzo.Code.Data.AVL.Value.du52))
name182 = "Map._.headTail"
d182 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.Maybe.Base.T22
d182 v0 v1 v2 v3 v4 v5 = du182 v3
du182 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.Maybe.Base.T22
du182 v0 = coe (MAlonzo.Code.Data.AVL.du296 (coe v0))
name184 = "Map._.initLast"
d184 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.Maybe.Base.T22
d184 v0 v1 v2 v3 v4 v5 = du184 v3
du184 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.Maybe.Base.T22
du184 v0 = coe (MAlonzo.Code.Data.AVL.du310 (coe v0))
name186 = "Map._.fromList"
d186 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T14] -> MAlonzo.Code.Data.AVL.T194
d186 v0 v1 v2 v3 v4 v5 = du186 v3
du186 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T14] -> MAlonzo.Code.Data.AVL.T194
du186 v0
  = coe
      (MAlonzo.Code.Data.AVL.du324
         (coe v0)
         (coe
            (\ v1 v2 -> MAlonzo.Code.Data.AVL.Value.C48 v2) erased
            (\ v1 v2 v3 v4 -> v4)))
name188 = "Map._.toList"
d188 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Data.AVL.T194 -> [MAlonzo.Code.Agda.Builtin.Sigma.T14]
d188 v0 v1 v2 v3 v4 v5 = du188
du188 ::
  MAlonzo.Code.Data.AVL.T194 -> [MAlonzo.Code.Agda.Builtin.Sigma.T14]
du188 = coe MAlonzo.Code.Data.AVL.du326
name202 = "Map._.unionWith"
d202 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) ->
  MAlonzo.Code.Data.AVL.T194 ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.AVL.T194
d202 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du202 v3 v8
du202 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  (AgdaAny -> MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) ->
  MAlonzo.Code.Data.AVL.T194 ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.AVL.T194
du202 v0 v1
  = coe
      (MAlonzo.Code.Data.AVL.du348
         (coe v0) (coe MAlonzo.Code.Data.AVL.Value.du52) (coe (\ v2 -> v1)))
name214 = "Map._.union"
d214 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Data.AVL.T194 ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.AVL.T194
d214 v0 v1 v2 v3 v4 v5 = du214 v3
du214 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Data.AVL.T194 ->
  MAlonzo.Code.Data.AVL.T194 -> MAlonzo.Code.Data.AVL.T194
du214 v0
  = coe
      (MAlonzo.Code.Data.AVL.du370
         (coe v0) (coe MAlonzo.Code.Data.AVL.Value.du52))
name216 = "Map._.unionsWith"
d216 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) ->
  [MAlonzo.Code.Data.AVL.T194] -> MAlonzo.Code.Data.AVL.T194
d216 v0 v1 v2 v3 v4 v5 v6 = du216 v3 v6
du216 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  (AgdaAny -> MAlonzo.Code.Data.Maybe.Base.T22 -> AgdaAny) ->
  [MAlonzo.Code.Data.AVL.T194] -> MAlonzo.Code.Data.AVL.T194
du216 v0 v1
  = coe
      (MAlonzo.Code.Data.AVL.du374
         (coe v0) (coe MAlonzo.Code.Data.AVL.Value.du52) (coe (\ v2 -> v1)))
name220 = "Map._.unions"
d220 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T1268 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> [MAlonzo.Code.Data.AVL.T194] -> MAlonzo.Code.Data.AVL.T194
d220 v0 v1 v2 v3 v4 v5 = du220 v3
du220 ::
  MAlonzo.Code.Relation.Binary.T1268 ->
  [MAlonzo.Code.Data.AVL.T194] -> MAlonzo.Code.Data.AVL.T194
du220 v0
  = coe
      (MAlonzo.Code.Data.AVL.du380
         (coe v0) (coe MAlonzo.Code.Data.AVL.Value.du52))
