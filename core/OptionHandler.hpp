/*
 *    This program is free software; you can redistribute it and/or modify
 *    it under the terms of the GNU General Public License as published by
 *    the Free Software Foundation; either version 2 of the License, or
 *    (at your option) any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 */

// import java.util.*;
#include <iostream>
#include <string> 
#include <vector> 
#include "Enumeration.hpp"

using namespace std; 

class OptionHandler {

  /**
   * Sets the OptionHandler's options using the given list. All options
   * will be set (or reset) during this call (i.e. incremental setting
   * of options is not possible).
   *
   * @param options the list of options as an array of strings
   * @exception Exception if an option is not supported
   */
  //@ requires options != NULL;
  //@ requires \nonNULLelements(options);
    virtual void setOptions(vector<string> options) = 0;

  /**
   * Gets the current option settings for the OptionHandler.
   *
   * @return the list of current option settings as an array of strings
   */
  //@ ensures \result != NULL;
  //@ ensures \nonNULLelements(\result);
  //virtual /*@pure@*/ string[] getOptions() = 0;
  virtual /*@pure@*/ vector<string> getOptions() = 0;
};
