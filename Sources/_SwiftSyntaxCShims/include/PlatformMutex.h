//===----------------------------------------------------------------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2024 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

#ifndef SWIFTSYNTAX_PLATFORMMUTEX_H
#define SWIFTSYNTAX_PLATFORMMUTEX_H

#ifdef __cplusplus
extern "C" {
#endif

typedef struct PlatformMutex {
  void *opaque;
} PlatformMutex;

__attribute__((swift_name("PlatformMutex.create()")))
PlatformMutex swiftsyntax_platform_mutex_create(void);

__attribute__((swift_name("PlatformMutex.lock(self:)")))
void swiftsyntax_platform_mutex_lock(PlatformMutex m);

__attribute__((swift_name("PlatformMutex.unlock(self:)")))
void swiftsyntax_platform_mutex_unlock(PlatformMutex m);

__attribute__((swift_name("PlatformMutex.destroy(self:)")))
void swiftsyntax_platform_mutex_destroy(PlatformMutex m);

#ifdef __cplusplus
} // extern "C"
#endif

#endif // SWIFTSYNTAX_PLATFORMMUTEX_H
