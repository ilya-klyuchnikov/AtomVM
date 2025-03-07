%
% This file is part of AtomVM.
%
% Copyright 2018 Davide Bettio <davide@uninstall.it>
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

-module(copy_terms11).

-export([start/0, loop/0]).

start() ->
    Pid = spawn(?MODULE, loop, []),
    Pid !
        {
            self(),
            {
                [
                    {[{1, 0}, {2, 1}, {3, 4}], [{4, 2}, {5, 5}, {6, 1}], 1},
                    {[{9, 3}, {1, 2}, {5, 5}], [{4, 3}, {2, 1}, {2, 3}], 4},
                    {[{2, 3}, {5, 7}, {8, 10}], [{1, 5}, {3, 2}, {2, 2}], 2}
                ]
            }
        },
    Res =
        receive
            Any -> Any
        end,
    Pid ! terminate,
    Res.

loop() ->
    case handle_request() of
        terminate ->
            terminate;
        ok ->
            loop()
    end.

handle_request() ->
    receive
        {Pid, {AList}} ->
            Pid ! process_all(AList, 0),
            ok;
        terminate ->
            terminate
    end.

process_all([], Acc) ->
    Acc;
process_all([{L1, L2, W} | T], Acc) ->
    {A, B} = dot(L1, L2, {0, 0}),
    process_all(T, Acc + (A * A + B * B) * W).

dot([], [], Acc) ->
    Acc;
dot([{HA_1, HA_2} | TA], [{HB_1, HB_2} | TB], Acc) ->
    dot(TA, TB, sum(Acc, {HA_1 * HB_1 - HA_2 * HB_2, HA_1 * HB_2 + HA_2 * HB_1})).

sum({A_1, A_2}, {B_1, B_2}) ->
    {A_1 + B_1, A_2 + B_2}.
