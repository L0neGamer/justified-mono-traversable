{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.Containers.Justified
  ( JContainer
  , unJustifyContainer
  , withJContainer

  , JKey
  , unJustifyKey

  , IsJustifiedSet (..)
  , IsJustifiedMap (..)
  ) where

import Data.Containers as Containers
import Data.Bifunctor (Bifunctor(first))
import Data.Hashable (Hashable)

import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as M

type role JContainer nominal representational
newtype JContainer ph cont = MkJContainer cont

unJustifyContainer :: JContainer ph cont -> cont
unJustifyContainer (MkJContainer cont) = cont

withJContainer :: cont -> (forall ph. JContainer ph cont -> r) -> r
withJContainer cont with = with (MkJContainer cont)

type role JKey nominal representational
newtype JKey ph key = MkJKey key
  deriving (Eq)

unJustifyKey :: JKey ph cont -> cont
unJustifyKey (MkJKey cont) = cont

class IsJustifiedSet set key where
  keysJ :: JContainer ph set -> [JKey ph key]
  memberJ :: key -> JContainer ph set -> Maybe (JKey ph key)

  default keysJ :: (SetContainer set, key ~ ContainerKey set) => JContainer ph set -> [JKey ph key]
  keysJ (MkJContainer set) = MkJKey <$> keys set

  default memberJ :: (SetContainer set, key ~ ContainerKey set) => key -> JContainer ph set ->  Maybe (JKey ph key)
  memberJ key (MkJContainer set) = if member key set then Just (MkJKey key) else Nothing

instance (Hashable k) => IsJustifiedSet (HM.HashMap k v) k
instance (Ord k) => IsJustifiedSet (M.Map k v) k

type JustifiedMapConstraint map key value = (IsMap map, key ~ ContainerKey map, value ~ MapValue map)

class IsJustifiedSet map key => IsJustifiedMap map key value | map key -> value where
  lookupJ :: JKey ph key -> JContainer ph map -> value
  memberMapJ :: key -> JContainer ph map -> Maybe (JKey ph key, value)
  adjustMapJ :: (value -> value) -> JKey ph key -> JContainer ph map -> JContainer ph map
  insertingWithJ ::
       (value -> value -> value)
    -> key
    -> value
    -> JContainer ph map
    -> (forall ph'. JKey ph' key -> (JKey ph key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  insertingJ ::
       key
    -> value
    -> JContainer ph map
    -> (forall ph'. JKey ph' key -> (JKey ph key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  unioningWithKeyJ ::
       (JKey phL key -> JKey phR key -> value -> value -> value)
    -> JContainer phL map
    -> JContainer phR map
    -> (forall ph'. (JKey phL key -> JKey ph' key) -> (JKey phR key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  unioningWithJ ::
       (value -> value -> value)
    -> JContainer phL map
    -> JContainer phR map
    -> (forall ph'. (JKey phL key -> JKey ph' key) -> (JKey phR key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  deletingJ ::
       key
    -> JContainer ph map
    -> (forall ph'. (JKey ph' key -> JKey ph key) -> JContainer ph' map -> r)
    -> r
  mapToListJ :: JContainer ph map -> [(JKey ph key, MapValue map)]
  filteringJ ::
       (value -> Bool)
    -> JContainer ph map
    -> (forall ph'. (JKey ph' key -> JKey ph key) -> JContainer ph' map -> r)
    -> r
  mapWithKeyJ ::
       (JKey ph key -> value -> value)
    -> JContainer ph map
    -> JContainer ph map
  mapKeysWithJ ::
       (value -> value -> value)
    -> (key -> key)
    -> JContainer ph map
    -> (forall ph'. (JKey ph key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r

  default lookupJ :: JustifiedMapConstraint map key value => JKey ph key -> JContainer ph map -> value
  lookupJ (MkJKey key) (MkJContainer map') = case Containers.lookup key map' of
    Just val -> val
    Nothing -> error "Data.Containers.Justified has been subverted; somehow a key was found that was not in the map"

  default memberMapJ :: key -> JContainer ph map -> Maybe (JKey ph key, value)
  memberMapJ key jMap = (\jKey -> (jKey, lookupJ jKey jMap)) <$> memberJ key jMap

  default adjustMapJ :: JustifiedMapConstraint map key value => (value -> value) -> JKey ph key -> JContainer ph map -> JContainer ph map
  adjustMapJ f (MkJKey key) (MkJContainer map') = MkJContainer $ adjustMap f key map'

  default insertingWithJ :: JustifiedMapConstraint map key value
    => (value -> value -> value)
    -> key
    -> value
    -> JContainer ph map
    -> (forall ph'. JKey ph' key -> (JKey ph key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  insertingWithJ f key val (MkJContainer map') withNewMap = withNewMap (MkJKey key) toNewKey (MkJContainer $ insertWith f key val map')
    where
    toNewKey (MkJKey key') = MkJKey key'

  default insertingJ ::
       key
    -> value
    -> JContainer ph map
    -> (forall ph'. JKey ph' key -> (JKey ph key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  insertingJ = insertingWithJ const

  default unioningWithKeyJ :: JustifiedMapConstraint map key value
    => (JKey phL key -> JKey phR key -> value -> value -> value)
    -> JContainer phL map
    -> JContainer phR map
    -> (forall ph'. (JKey phL key -> JKey ph' key) -> (JKey phR key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  unioningWithKeyJ f (MkJContainer mapL) (MkJContainer mapR) withNewMap = withNewMap fromLeftKey fromRightKey (MkJContainer $ unionWithKey (\key -> f (MkJKey key) (MkJKey key)) mapL mapR)
    where
    fromLeftKey (MkJKey key) = MkJKey key
    fromRightKey (MkJKey key) = MkJKey key

  default unioningWithJ ::
       (value -> value -> value)
    -> JContainer phL map
    -> JContainer phR map
    -> (forall ph'. (JKey phL key -> JKey ph' key) -> (JKey phR key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  unioningWithJ f = unioningWithKeyJ (\_ _ -> f)

  unioningJ ::
       JContainer phL map
    -> JContainer phR map
    -> (forall ph'. (JKey phL key -> JKey ph' key) -> (JKey phR key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  unioningJ = unioningWithJ const

  default deletingJ :: JustifiedMapConstraint map key value
    => key
    -> JContainer ph map
    -> (forall ph'. (JKey ph' key -> JKey ph key) -> JContainer ph' map -> r)
    -> r
  deletingJ key (MkJContainer map') withNewMap = withNewMap toOldKey (MkJContainer $ deleteMap key map')
    where
    toOldKey (MkJKey key') = MkJKey key'

  default mapToListJ :: JustifiedMapConstraint map key value => JContainer ph map -> [(JKey ph key, MapValue map)]
  mapToListJ (MkJContainer map') = first MkJKey <$> mapToList map'

  default filteringJ :: JustifiedMapConstraint map key value 
    => (value -> Bool)
    -> JContainer ph map
    -> (forall ph'. (JKey ph' key -> JKey ph key) -> JContainer ph' map -> r)
    -> r
  filteringJ pred' (MkJContainer map') withNewMap = withNewMap toOldKey (MkJContainer $ filterMap pred' map')
    where
    toOldKey (MkJKey key') = MkJKey key'

  default mapWithKeyJ :: JustifiedMapConstraint map key value
    => (JKey ph key -> value -> value)
    -> JContainer ph map
    -> JContainer ph map
  mapWithKeyJ f (MkJContainer map') = MkJContainer $ mapWithKey (f . MkJKey) map'

  default mapKeysWithJ :: JustifiedMapConstraint map key value
    => (value -> value -> value)
    -> (key -> key)
    -> JContainer ph map
    -> (forall ph'. (JKey ph key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  mapKeysWithJ comb conv (MkJContainer map') withNewMap = withNewMap toNewKey (MkJContainer $ omapKeysWith comb conv map')
    where
    toNewKey (MkJKey key) = MkJKey $ conv key

instance (Hashable k) => IsJustifiedMap (HM.HashMap k v) k v
instance (Ord k) => IsJustifiedMap (M.Map k v) k v
