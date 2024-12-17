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

#include "PlatformMutex.h"

#ifdef __APPLE__
#include <os/lock.h>
PlatformMutex swiftsyntax_platform_mutex_create() {
  return {new os_unfair_lock(OS_UNFAIR_LOCK_INIT)};
}

__attribute__((swift_name("PlatformMutex.lock(self:)")))
void swiftsyntax_platform_mutex_lock(PlatformMutex m) {
  os_unfair_lock_lock(static_cast<os_unfair_lock_t>(m.opaque));
}

__attribute__((swift_name("PlatformMutex.unlock(self:)")))
void swiftsyntax_platform_mutex_unlock(PlatformMutex m) {
  os_unfair_lock_unlock(static_cast<os_unfair_lock_t>(m.opaque));
}

__attribute__((swift_name("PlatformMutex.destroy(self:)")))
void swiftsyntax_platform_mutex_destroy(PlatformMutex m) {
  delete static_cast<os_unfair_lock_t>(m.opaque);
}

#else
#include <mutex>

PlatformMutex swiftsyntax_platform_mutex_create() {
  return {new std::mutex()};
}

__attribute__((swift_name("PlatformMutex.lock(self:)")))
void swiftsyntax_platform_mutex_lock(PlatformMutex m) {
  return static_cast<std::mutex *>(m.opaque)->lock();
}

__attribute__((swift_name("PlatformMutex.unlock(self:)")))
void swiftsyntax_platform_mutex_unlock(PlatformMutex m) {
  return static_cast<std::mutex *>(m.opaque)->unlock();
}

__attribute__((swift_name("PlatformMutex.destroy(self:)")))
void swiftsyntax_platform_mutex_destroy(PlatformMutex m) {
  delete static_cast<std::mutex *>(m.opaque);
}
#endif
