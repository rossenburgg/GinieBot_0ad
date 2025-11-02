"""Runtime compatibility shims for legacy dependencies.

Render's build step imports ``sleekxmpp`` while compiling wheels. Newer
Python versions (>3.10) removed several aliases from the ``collections``
module, so we mirror the missing symbols from ``collections.abc`` to
maintain compatibility.
"""

from __future__ import annotations

import collections
import collections.abc

# SleekXMPP still imports the old names from ``collections`` during its
# setup routine. Populate them on demand so installation succeeds on modern
# interpreters (3.11+).
for name in ("MutableMapping", "MutableSet", "MutableSequence"):
    if not hasattr(collections, name) and hasattr(collections.abc, name):
        setattr(collections, name, getattr(collections.abc, name))
