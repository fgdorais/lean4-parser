/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
public import Batteries
public import UnicodeBasic

public instance : Std.Stream String.Slice Char where
  next? s := s.front? >>= fun c => return (c, s.drop 1)
