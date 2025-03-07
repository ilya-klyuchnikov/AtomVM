%
% This file is part of AtomVM.
%
% Copyright 2023 Fred Dushin <fred@dushin.net>
%
% Licensed under the Apache License, Version 2.0 (the "License")
% you may not use this file except in compliance with the License.
% You may obtain a copy of the License at
%
%    http://www.apache.org/licenses/LICENSE-2.0
%
% Unless required by applicable law or agreed to in writing, software
% distributed under the License is distributed on an "AS IS" BASIS,
% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
% See the License for the specific language governing permissions and
% limitations under the License.
%
% SPDX-License-Identifier: Apache-2.0 OR LGPL-2.1-or-later
%
-module(crypto).

-export([
    hash/2
]).

-type hash_algorithm() :: md5 | sha | sha224 | sha256 | sha384 | sha512.
-type digest() :: binary().

%%-----------------------------------------------------------------------------
%% @param   Type the hash algorithm
%% @param   Data the data to hash
%% @returns Returns the result of hashing the supplied data using the supplied
%%          hash algorithm.
%% @doc     Hash data using a specified hash algorithm.
%% @end
%%-----------------------------------------------------------------------------
-spec hash(Type :: hash_algorithm(), Data :: iolist()) -> digest().
hash(_Type, _Data) ->
    erlang:nif_error(undefined).
