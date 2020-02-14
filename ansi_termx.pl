/*
  BSD 2-Clause License

  Copyright (c) 2019, Can Bican
  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are met:

  * Redistributions of source code must retain the above copyright notice, this
    list of conditions and the following disclaimer.

  * Redistributions in binary form must reproduce the above copyright notice,
    this list of conditions and the following disclaimer in the documentation
    and/or other materials provided with the distribution.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

:- module(ansi_termx, [
  clear_all_tabs/0,
  clear_screen/0,
  clear_tab/0,
  color/1,
  color/5,
  cursor_move/2,
  cursor_position/2,
  cursor_save/0,
  cursor_unsave/0,
  reset/0,
  screen_size/2,
  scroll/2,
  set_tab/0,
  style/1
  ]).

/** <module> ANSI terminal manipulation predicates
This module provides predicates for manipulating ANSI terminals. It doesn't
aim to cover all of the features, focusing on functionality for fancier
output. The extra *x* at the end of the package name aims to disambiguate the
SWI-Prolog library [[library(ansi_term)][https://www.swi-prolog.org/pldoc/man?section=ansiterm]].

@see [[library(ansi_term)][https://www.swi-prolog.org/pldoc/man?section=ansiterm]]
@author Can Bican
@license BSD 2-clause
*/

color_code(default, 39, 49).
color_code(black, 30, 40).
color_code(red, 31, 41).
color_code(green, 32, 42).
color_code(yellow, 33, 43).
color_code(blue, 34, 44).
color_code(magenta, 35, 45).
color_code(cyan, 36, 46).
color_code(white, 37, 47).
color_code(bright_black, 90, 100).
color_code(bright_red, 91, 101).
color_code(bright_green, 92, 102).
color_code(bright_yellow, 93, 103).
color_code(bright_blue, 94, 104).
color_code(bright_magenta, 95, 105).
color_code(bright_cyan, 96, 106).
color_code(bright_white, 97, 107).

style_code(default, 0).
style_code(bold, 1).
style_code(dim, 2).
style_code(italic, 3).
style_code(underline, 4).
style_code(reverse, 7).
style_code(crossed_out, 9).

scroll_direction(up, 'S').
scroll_direction(down, 'T').

cursor_direction(up, 'A').
cursor_direction(down, 'B').
cursor_direction(forward, 'C').
cursor_direction(backward, 'D').

%! clear_all_tabs is det
%  Clear all tabs
clear_all_tabs :- out_tty('[3g').

%! clear_screen is det
%  Clear the screen and move cursor to topleft of the screen
clear_screen :-
  out_tty('[2J'),
  goto_position(0, 0).

%! clear_tab is det
%  Clear the tab on the current cursor position
clear_tab :- out_tty('[g').

%! color(-Color:atom) is multi
%  Enumerates available colors.
%
%  @arg Color is a valid color
%
color(Color) :-
  color_code(Color, _, _).

%! color(+Color:atom, +Background:atom, +Styles:list(atom), +Input:any, -Output:string) is semidet
%  Generates text of input with a style.
%
%  @arg Color is one of `default`, `black`, `red`, `green`, `yellow`,
%  `blue`, `magenta`, `cyan`, `white`, `bright_black`, `bright_red`, `bright_green`,
%  `bright_yellow`, `bright_blue`, `bright_magenta`, `bright_cyan` or `bright_white`.
%
%  @arg Background is one of `default`, `black`, `red`, `green`, `yellow`,
%  `blue`, `magenta`, `cyan`, `white`, `bright_black`, `bright_red`, `bright_green`,
%  `bright_yellow`, `bright_blue`, `bright_magenta`, `bright_cyan` or `bright_white`.
%
%  @arg Styles is one or more of `default`, `bold`, `dim`, `italic`, `underline`,
%  `reverse` or `crossed_out`.
%
%  @arg Input is any kind of variable that can be fed to ~w modifier of format/3.
%
%  @arg Output is the resulting string that can be printed by printing predicate.

color(Color, Background, Styles, Input, Output) :-
  color_code(Color, ColorCode, _),
  color_code(Background, _, BackgroundCode),
  maplist(style_code, Styles, StyleCodes),
  atomic_list_concat(StyleCodes, ';', StyleCode),
  format(atom(Output), '\033[~w;~w;~wm~w\033[0m',[StyleCode, ColorCode, BackgroundCode, Input]).

%! cursor_move(+Count:int, +Direction:atom) is semidet
%  Relative cursor movement.
%
%  @arg Count is number of steps to move in Direction.
%  @arg Direction is one of `up`, `down`, `forward` or `backward`.
%
cursor_move(Count, Direction) :-
  number(Count),
  cursor_direction(Direction, D),
  format(atom(Out),'[~w~w', [Count, D]),
  out_tty(Out).

%! cursor_position(?Row:int, ?Column:int) is det
%  Queries and sets the cursor position.
%
%  @arg Row is the row of the screen. It can be queried or set.
%  @arg Column is the column of the screen. It can be queried or set.
%
cursor_position(Row, Column) :-
  \+ ground(Row),
  \+ ground(Column),
  !,
  read_screen_position_response(Row, Column).

cursor_position(NewRow, Column) :-
  ground(NewRow),
  \+ ground(Column),
  !,
  read_screen_position_response(_, Column),
  goto_position(NewRow, Column).

cursor_position(Row, NewColumn) :-
  ground(NewColumn),
  \+ ground(Row),
  !,
  read_screen_position_response(Row, _),
  goto_position(Row, NewColumn).

cursor_position(Row, Column) :-
  goto_position(Row, Column).

%! cursor_save is det
%  Saves the current position of the cursor, to be retrieved later by cursor_unsave/0.
cursor_save :- out_tty('[s').

%! cursor_unsave is det
%  Restores the current position of the cursor, previously saved by cursor_save/0.
cursor_unsave :- out_tty('[u').

%! reset is det
%  Resets the terminal
reset :- out_tty('c').

%! screen_size(-Rows:int, -Columns:int) is det
%  Determines the screen size.
%
%  @arg Rows is the height of the current terminal.
%  @arg Columns is the width of the current terminal.
%
screen_size(Rows, Columns) :-
  cursor_position(OR, OC),
  cursor_position(9999, 9999),
  cursor_position(Rows, Columns),
  cursor_position(OR, OC).

%! scroll(+Lines:int, +Direction:atom) is semidet
%  Scrolls the screen up or down, depending on the direction.
%
%  @arg Lines number of lines to scroll
%  @arg Direction *up* or *down*
%
scroll(Count, Direction) :-
  number(Count),
  scroll_direction(Direction, D),
  format(atom(Out),'[~w~w', [Count, D]),
  out_tty(Out).

%! set_tab is det
%  Set a tab on the current cursor position
set_tab :- out_tty('H').

%! style(-Style:atom) is multi
%  Enumerates all styles.
%
%  @arg Style is a valid style
%
style(Style) :-
  style_code(Style, _).
 
goto_position(Row, Column) :-
  format(atom(Out), '[~w;~wH', [Row, Column]),
  out_tty(Out).

read_screen_position_response(Row, Column) :-
  out_tty('[6n'),
  read_input_upto(82, [27, 91|ResponseCodes]),
  !,
  string_codes(ResponseString, ResponseCodes),
  split_string(ResponseString, ';', "", [RowString, ColumnString]),
  number_codes(Row, RowString),
  number_codes(Column, ColumnString).
read_screen_position_response(0, 0).

read_input_upto(S, Result) :-
  read_tty_char(Char),
  (  Char=S
  -> Result=[]
  ;  read_input_upto(S, SubResult),
     Result=[Char|SubResult]
  ).

read_tty_char(Char) :-
  is_tty,
  get_single_char(Char).

out_tty(Out) :-
  is_tty,
  !,
  format('\033~w', [Out]).
out_tty(_).

is_tty :-
  stream_property(current_output, tty(true)),
  current_prolog_flag(color_term, true).

