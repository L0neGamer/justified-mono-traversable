{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

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

type role JContainer nominal nominal
newtype JContainer ph cont = MkJContainer cont
  deriving (Show, Eq, Ord)

unJustifyContainer :: JContainer ph cont -> cont
unJustifyContainer (MkJContainer cont) = cont

withJContainer :: cont -> (forall ph. JContainer ph cont -> r) -> r
withJContainer cont with = with (MkJContainer cont)

type role JKey nominal nominal
newtype JKey ph key = MkJKey key
type JKeyOf ph set = JKey ph (ContainerKey set)

unJustifyKey :: JKey ph cont -> cont
unJustifyKey (MkJKey cont) = cont

class SetContainer set => IsJustifiedSet set where
  keysJ :: JContainer ph set -> [JKeyOf ph set]
  keysJ (MkJContainer set) = MkJKey <$> keys set

  memberJ :: ContainerKey set -> JContainer ph set -> Maybe (JKeyOf ph set)
  memberJ key (MkJContainer set) = if member key set then Just (MkJKey key) else Nothing

instance SetContainer set => IsJustifiedSet set where

class (IsMap map, IsJustifiedSet map) => IsJustifiedMap map where
  lookupJ :: JKeyOf ph map -> JContainer ph map -> MapValue map
  lookupJ (MkJKey key) (MkJContainer map') = case Containers.lookup key map' of
    Just val -> val
    Nothing -> error "Data.Containers.Justified has been subverted; somehow a key was found that was not in the map"

  memberMapJ :: ContainerKey map -> JContainer ph map -> Maybe (JKeyOf ph map, MapValue map)
  memberMapJ key jMap = (\jKey -> (jKey, lookupJ jKey jMap)) <$> memberJ key jMap

  adjustMapJ :: (MapValue map -> MapValue map) -> JKeyOf ph map -> JContainer ph map -> JContainer ph map
  adjustMapJ f (MkJKey key) (MkJContainer map') = MkJContainer $ adjustMap f key map'

  insertingWithJ ::
       (MapValue map -> MapValue map -> MapValue map)
    -> ContainerKey map
    -> MapValue map
    -> JContainer ph map
    -> (forall ph'. JKeyOf ph' map -> (JKeyOf ph map -> JKeyOf ph' map) -> JContainer ph' map -> r)
    -> r
  insertingWithJ f key val (MkJContainer map') withNewMap = withNewMap (MkJKey key) toNewKey (MkJContainer $ insertWith f key val map')
    where
    toNewKey (MkJKey key') = MkJKey key'

  insertingJ ::
       ContainerKey map
    -> MapValue map
    -> JContainer ph map
    -> (forall ph'. JKeyOf ph' map -> (JKeyOf ph map -> JKeyOf ph' map) -> JContainer ph' map -> r)
    -> r
  insertingJ = insertingWithJ const

  unioningWithKeyJ ::
       (JKeyOf phL map -> JKeyOf phR map -> MapValue map -> MapValue map -> MapValue map)
    -> JContainer phL map
    -> JContainer phR map
    -> (forall ph'. (JKeyOf phL map -> JKeyOf ph' map) -> (JKeyOf phR map -> JKeyOf ph' map) -> JContainer ph' map -> r)
    -> r
  unioningWithKeyJ f (MkJContainer mapL) (MkJContainer mapR) withNewMap = withNewMap fromLeftKey fromRightKey (MkJContainer $ unionWithKey (\key -> f (MkJKey key) (MkJKey key)) mapL mapR)
    where
    fromLeftKey (MkJKey key) = MkJKey key
    fromRightKey (MkJKey key) = MkJKey key

  unioningWithJ ::
       (MapValue map -> MapValue map -> MapValue map)
    -> JContainer phL map
    -> JContainer phR map
    -> (forall ph'. (JKeyOf phL map -> JKeyOf ph' map) -> (JKeyOf phR map -> JKeyOf ph' map) -> JContainer ph' map -> r)
    -> r
  unioningWithJ f = unioningWithKeyJ (\_ _ -> f)

  unioningJ ::
       JContainer phL map
    -> JContainer phR map
    -> (forall ph'. (JKeyOf phL map -> JKeyOf ph' map) -> (JKeyOf phR map -> JKeyOf ph' map) -> JContainer ph' map -> r)
    -> r
  unioningJ = unioningWithJ const

  deletingJ ::
       ContainerKey map
    -> JContainer ph map
    -> (forall ph'. (JKeyOf ph' map -> JKeyOf ph map) -> JContainer ph' map -> r)
    -> r
  deletingJ key (MkJContainer map') withNewMap = withNewMap toOldKey (MkJContainer $ deleteMap key map')
    where
    toOldKey (MkJKey key') = MkJKey key'

  mapToListJ :: JContainer ph map -> [(JKeyOf ph map, MapValue map)]
  mapToListJ (MkJContainer map') = first MkJKey <$> mapToList map'

  filteringJ ::
       (MapValue map -> Bool)
    -> JContainer ph map
    -> (forall ph'. (JKeyOf ph' map -> JKeyOf ph map) -> JContainer ph' map -> r)
    -> r
  filteringJ pred' (MkJContainer map') withNewMap = withNewMap toOldKey (MkJContainer $ filterMap pred' map')
    where
    toOldKey (MkJKey key') = MkJKey key'

  mapWithKeyJ ::
       (JKeyOf ph map -> MapValue map -> MapValue map)
    -> JContainer ph map
    -> JContainer ph map
  mapWithKeyJ f (MkJContainer map') = MkJContainer $ mapWithKey (f . MkJKey) map'

  omapKeysWithJ ::
       (MapValue map -> MapValue map -> MapValue map)
    -> (ContainerKey map -> ContainerKey map)
    -> JContainer ph map
    -> (forall ph'. (JKeyOf ph map -> JKeyOf ph' map) -> JContainer ph' map -> r)
    -> r
  omapKeysWithJ comb conv (MkJContainer map') withNewMap = withNewMap toNewKey (MkJContainer $ omapKeysWith comb conv map')
    where
    toNewKey (MkJKey key) = MkJKey $ conv key

instance (IsMap map, IsJustifiedSet map) => IsJustifiedMap map where
