-- | Data structures and typeclasses for justifiable containers; that is, one must prove that a container has a key in it before you can use that key. As a result, you can then use that key freely on that container, theoretically without having to prove its presence again.
--

{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RoleAnnotations        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}

module Data.Containers.Justified
  (
  -- ** Justified container operations
    JContainer
  , unJustifyContainer
  , withJContainer

  -- ** Justified key
  , JKey
  , unJustifyKey

  -- ** Justified containers typeclasses
  , IsJustifiedSet (..)
  , IsJustifiedMap (..)

  -- ***
  , JustifiedMapConstraint
  ) where

import Data.Containers as Containers (IsMap (MapValue, adjustMap, deleteMap, filterMap, insertWith, lookup, mapWithKey, omapKeysWith, unionWithKey),
                                      SetContainer (ContainerKey, keys, member))
import Data.Hashable   (Hashable)

import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap.Strict  as IM
import qualified Data.Map.Strict     as M

-- | A justified container that can be trusted to have operations that have a
-- level risk otherwise, such as lookups that are normally failable.
--
-- Can only be constructed using `withJContainer`.
newtype JContainer ph cont = MkJContainer cont
type role JContainer nominal representational

-- | Extract the container from its justified wrapping.
unJustifyContainer :: JContainer ph cont -> cont
unJustifyContainer (MkJContainer cont) = cont

-- | Using a continuation and existentially defined types, make it so we can
-- justify the operations we perform on the container.
--
-- Using the phantom type and the `forall`, we can guarantee that nothing
-- leaks out, and that operations are safe.
--
-- Mostly useful when `cont` has an `IsJustifiedMap` instance.
withJContainer :: cont -> (forall ph. JContainer ph cont -> r) -> r
withJContainer cont with = with (MkJContainer cont)

-- | A key of a value that is known to be in a container. Due to existential
-- types in `withJContainer`, each key must be associated with a given container,
-- and that means you shouldn't be able to use justified keys with different
-- containers.
newtype JKey ph key = MkJKey key
  deriving (Eq)
type role JKey nominal representational

-- | Unwrap a justified key.
unJustifyKey :: JKey ph key -> key
unJustifyKey (MkJKey key) = key

-- | Relation between keys and sets, giving methods to get justified keys from
-- a container.
--
-- Not much point defining this for sets ironically enough, since any operations
-- relating to checking contents are trivial when a JKey is present.
class IsJustifiedSet set key where
  {-# INLINE keysJ #-}
  -- | Get all the keys in the container.
  keysJ :: JContainer ph set -> [JKey ph key]
  {-# INLINE memberJ #-}
  -- | Get proof that a key exists in the container.
  --
  -- If there were a function `memberJBool :: JKey ph key -> JContainer ph set -> Bool`,
  -- it should always return True, and hence is not provided here.
  memberJ :: key -> JContainer ph set -> Maybe (JKey ph key)

  default keysJ :: (SetContainer set, key ~ ContainerKey set) => JContainer ph set -> [JKey ph key]
  keysJ (MkJContainer set) = MkJKey <$> keys set

  default memberJ :: (SetContainer set, key ~ ContainerKey set) => key -> JContainer ph set ->  Maybe (JKey ph key)
  memberJ key (MkJContainer set) = if member key set then Just (MkJKey key) else Nothing

instance (Hashable k) => IsJustifiedSet (HM.HashMap k v) k
instance (Ord k) => IsJustifiedSet (M.Map k v) k
instance IsJustifiedSet (IM.IntMap v) Int

-- | Convenience constraint for the default definitions.
type JustifiedMapConstraint map key value = (IsMap map, key ~ ContainerKey map, value ~ MapValue map)

-- | The class of types that we can get justified keys from, and using those
-- justified keys we can guarantee certain operations are unfailable, such as
-- looking up a value, inserting, unioning, and deleting.
--
-- Minimal definition would include:
-- `lookupJ`, `adjustMapJ`, `insertingWithJ`, `unioningWithKeyJ`, `deletingJ`, `filteringJ`, `mapWithKeyJ`, `mapKeysWithJ`
--
-- The following methods are defined in terms of other methods, and thus don't
-- have to by defined be a user unless greater efficiency is possible:
-- `memberMapJ`, `insertingJ`, `unioningWithJ`, `unioningJ`, `mapToListJ`
class IsJustifiedSet map key => IsJustifiedMap map key value | map key -> value where
  {-# INLINE lookupJ #-}
  -- | Using the fact that we know that the key is in the container, get a value
  -- from the container.
  lookupJ :: JKey ph key -> JContainer ph map -> value
  {-# INLINE memberMapJ #-}
  -- | Lookup a key in the container, possibly returning proof of the key and the
  -- value associated with that key.
  --
  -- By default, uses `lookupJ` and `memberJ`, but can be redefined if it can be
  -- more efficiently defined.
  memberMapJ :: key -> JContainer ph map -> Maybe (JKey ph key, value)
  memberMapJ key jMap = (\jKey -> (jKey, lookupJ jKey jMap)) <$> memberJ key jMap
  {-# INLINE adjustMapJ #-}
  -- | Adjust the value of the given key in the map. Guaranteed to make a change,
  -- since we know that the key is in the map.
  adjustMapJ :: (value -> value) -> JKey ph key -> JContainer ph map -> JContainer ph map
  {-# INLINE insertingWithJ #-}
  -- | Insert a value into the container, giving a way to combine the new and
  -- old values if there was previously a value, and then use a continuation to
  -- operate on the new map, with the new key, and ways to get new keys from the
  -- old keys.
  insertingWithJ ::
       (value -> value -> value)
    -> key
    -> value
    -> JContainer ph map
    -> (forall ph'. JKey ph' key -> (JKey ph key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  {-# INLINE insertingJ #-}
  -- | As with `insertingWithJ`, but uses `const` to always use the new value.
  --
  -- Defined using `insertingWithJ`.
  insertingJ ::
       key
    -> value
    -> JContainer ph map
    -> (forall ph'. JKey ph' key -> (JKey ph key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  insertingJ = insertingWithJ const
  {-# INLINE unioningWithKeyJ #-}
  -- | Combine two justified containers using a combining function that takes the left
  -- key and the right key, as well as the values to combine.
  unioningWithKeyJ ::
       (JKey phL key -> JKey phR key -> value -> value -> value)
    -> JContainer phL map
    -> JContainer phR map
    -> (forall ph'. (JKey phL key -> JKey ph' key) -> (JKey phR key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  {-# INLINE unioningWithJ #-}
  -- | As with `unioningWithKeyJ`, but ignores the key values.
  --
  -- Defined using `unioningWithKeyJ`.
  unioningWithJ ::
       (value -> value -> value)
    -> JContainer phL map
    -> JContainer phR map
    -> (forall ph'. (JKey phL key -> JKey ph' key) -> (JKey phR key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  unioningWithJ f = unioningWithKeyJ (\_ _ -> f)
  {-# INLINE unioningJ #-}
  -- | As with `unioningWithJ`, but always takes the value in the left container.
  --
  -- Defined using `unioningWithJ`.
  unioningJ ::
       JContainer phL map
    -> JContainer phR map
    -> (forall ph'. (JKey phL key -> JKey ph' key) -> (JKey phR key -> JKey ph' key) -> JContainer ph' map -> r)
    -> r
  unioningJ = unioningWithJ const
  {-# INLINE deletingJ #-}
  -- | Possibly deletes a given key from the container, then uses a continuation
  -- to give a way to convert the new keys into the old keys.
  deletingJ ::
       key
    -> JContainer ph map
    -> (forall ph'. (JKey ph' key -> JKey ph key) -> JContainer ph' map -> r)
    -> r
  {-# INLINE mapToListJ #-}
  -- | Get all the key-value pairs in the container.
  --
  -- Uses `lookupJ` and `keysJ` in the default implementation.
  mapToListJ :: JContainer ph map -> [(JKey ph key, value)]
  mapToListJ container = (\k -> (k, lookupJ k container)) <$> keysJ container
  {-# INLINE filteringJ #-}
  -- | Filter the container based on each value, then use a continuation to
  -- use the modified container.
  filteringJ ::
       (value -> Bool)
    -> JContainer ph map
    -> (forall ph'. (JKey ph' key -> JKey ph key) -> JContainer ph' map -> r)
    -> r
  {-# INLINE mapWithKeyJ #-}
  -- | Modify the value of each element of the container, using the key as well.
  mapWithKeyJ ::
       (JKey ph key -> value -> value)
    -> JContainer ph map
    -> JContainer ph map
  {-# INLINE mapKeysWithJ #-}
  -- | Map over the keys of a container, and combine values using a given binary
  -- operation, using a continuation to process the new container.
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

  default deletingJ :: JustifiedMapConstraint map key value
    => key
    -> JContainer ph map
    -> (forall ph'. (JKey ph' key -> JKey ph key) -> JContainer ph' map -> r)
    -> r
  deletingJ key (MkJContainer map') withNewMap = withNewMap toOldKey (MkJContainer $ deleteMap key map')
    where
    toOldKey (MkJKey key') = MkJKey key'

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
instance IsJustifiedMap (IM.IntMap v) Int v
