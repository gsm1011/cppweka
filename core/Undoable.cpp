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

/*
 *    Copyable.cpp
 *    Copyright (C) 2005 University of Waikato, Hamilton, New Zealand
 *
 */

// package weka.core;

/**
 * Interface implemented by classes that support undo.
 *
 * @author FracPete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 1.2 $
 */
class Undoable {
public:
  /**
   * returns whether undo support is enabled
   */
  virtual bool isUndoEnabled() = 0;
  
  /**
   * sets whether undo support is enabled
   */
  virtual void setUndoEnabled(bool enabled) = 0;

  /**
   * removes the undo history
   */
  virtual void clearUndo() = 0;
  
  /**
   * returns whether an undo is possible, i.e. whether there are any undo points
   * saved so far
   * 
   * @return returns TRUE if there is an undo possible 
   */
  virtual bool canUndo() = 0;
  
  /**
   * undoes the last action
   */
  virtual void undo() = 0;
  
  /**
   * adds an undo point to the undo history 
   */
  virtual void addUndoPoint() = 0;
};
