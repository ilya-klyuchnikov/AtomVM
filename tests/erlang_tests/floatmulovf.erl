%
% This file is part of AtomVM.
%
% Copyright 2019 Davide Bettio <davide@uninstall.it>
%
% Licensed under the Apache License, Version 2.0 (the "License");
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

-module(floatmulovf).

-export([start/0]).

start() ->
    ok = test_mulovf_bif(),
    ok = test_mulovf_isfloat(),
    0.

test_mulovf_bif() ->
    ok = mul_bif(max_float(), 2.0),
    ok.

test_mulovf_isfloat() ->
    ok = mul_isfloat(max_float(), 2.0),
    ok.

mul_bif(A, B) ->
    try id(A) * id(B) of
        _C ->
            fail_no_ex
    catch
        error:badarith -> ok;
        _:_ -> fail_other_ex
    end.

id(I) ->
    I.

mul_isfloat(A, B) when is_float(A) andalso is_float(B) ->
    try A * B of
        _C ->
            fail_no_ex
    catch
        error:badarith -> ok;
        _:_ -> fail_other_ex
    end.

max_float() ->
    case erlang:system_info(machine) of
        "BEAM" ->
            1.7976931348623157e308;
        "ATOM" ->
            case erlang:system_info(avm_floatsize) of
                4 -> 3.4028234664e38;
                8 -> 1.7976931348623157e308
            end
    end.
