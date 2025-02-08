/*
 * ShortcutsOptionPane.java - Shortcuts options panel
 * Copyright (C) 1999, 2000, 2001 Slava Pestov
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package org.gjt.sp.jedit.options;

import javax.swing.table.*;
import javax.swing.*;
import java.awt.event.*;
import java.awt.*;
import java.util.*;
import org.gjt.sp.jedit.gui.GrabKeyDialog;
import org.gjt.sp.jedit.*;

/**
 * Generic key binding editor.
 * @author Slava Pestov
 * @version $Id: ShortcutsOptionPane.java,v 1.8 2001/02/05 09:15:30 sp Exp $
 */
public abstract class ShortcutsOptionPane extends AbstractOptionPane
{
	public ShortcutsOptionPane(String name)
	{
		super(name);
	}

	// protected members
	protected abstract Vector createBindings();

	protected void _init()
	{
		setLayout(new BorderLayout());

		keyModel = new ShortcutsModel(createBindings());;
		keyTable = new JTable(keyModel);
		keyTable.getTableHeader().setReorderingAllowed(false);
		keyTable.getTableHeader().addMouseListener(new HeaderMouseHandler());
		keyTable.addMouseListener(new TableMouseHandler());
		Dimension d = keyTable.getPreferredSize();
		d.height = Math.min(d.height,200);
		JScrollPane scroller = new JScrollPane(keyTable);
		scroller.setPreferredSize(d);

		add(BorderLayout.CENTER,scroller);
	}

	protected void _save()
	{
		if(keyTable.getCellEditor() != null)
			keyTable.getCellEditor().stopCellEditing();

		keyModel.save();
	}

	// private members
	private JTable keyTable;
	private ShortcutsModel keyModel;

	static class KeyBinding
	{
		KeyBinding(String name, String label,
			String shortcut1, String shortcut2)
		{
			this.name = name;
			this.label = label;
			this.shortcut1 = shortcut1;
			this.shortcut2 = shortcut2;
		}

		String name;
		String label;
		String shortcut1, shortcut2;
	}

	class HeaderMouseHandler extends MouseAdapter
	{
		public void mouseClicked(MouseEvent evt)
		{
			switch(keyTable.getTableHeader().columnAtPoint(evt.getPoint()))
			{
			case 0:
				keyModel.sort(0);
				break;
			case 1:
				keyModel.sort(1);
				break;
			case 2:
				keyModel.sort(2);
				break;
			}
		}
	}

	class TableMouseHandler extends MouseAdapter
	{
		public void mouseClicked(MouseEvent evt)
		{
			int row = keyTable.getSelectedRow();
			int column = keyTable.getSelectedColumn();
			if(column != 0)
			{
				String command = (String)keyModel.getValueAt(row,0);

				String shortcut = new GrabKeyDialog(
					ShortcutsOptionPane.this,
					command).getShortcut();
				if(shortcut != null)
					keyModel.setValueAt(shortcut,row,column);
			}
		}
	}
}

class ShortcutsModel extends AbstractTableModel
{
	private Vector bindings;

	ShortcutsModel(Vector bindings)
	{
		this.bindings = bindings;
		sort(0);
	}

	public void sort(int col)
	{
		MiscUtilities.quicksort(bindings,new KeyCompare(col));
		fireTableDataChanged();
	}

	public int getColumnCount()
	{
		return 3;
	}

	public int getRowCount()
	{
		return bindings.size();
	}

	public Object getValueAt(int row, int col)
	{
		ShortcutsOptionPane.KeyBinding binding
			= (ShortcutsOptionPane.KeyBinding)
			bindings.elementAt(row);
		switch(col)
		{
		case 0:
			return binding.label;
		case 1:
			return binding.shortcut1;
		case 2:
			return binding.shortcut2;
		default:
			return null;
		}
	}

	public void setValueAt(Object value, int row, int col)
	{
		if(col == 0)
			return;

		ShortcutsOptionPane.KeyBinding binding = (ShortcutsOptionPane.KeyBinding)
			bindings.elementAt(row);

		if(col == 1)
			binding.shortcut1 = (String)value;
		else if(col == 2)
			binding.shortcut2 = (String)value;

		fireTableRowsUpdated(row,row);
	}

	public String getColumnName(int index)
	{
		switch(index)
		{
		case 0:
			return jEdit.getProperty("options.keys.name");
		case 1:
			return jEdit.getProperty("options.keys.shortcut1");
		case 2:
			return jEdit.getProperty("options.keys.shortcut2");
		default:
			return null;
		}
	}

	public void save()
	{
		for(int i = 0; i < bindings.size(); i++)
		{
			ShortcutsOptionPane.KeyBinding binding
				= (ShortcutsOptionPane.KeyBinding)
				bindings.elementAt(i);
			jEdit.setProperty(binding.name + ".shortcut",binding.shortcut1);
			jEdit.setProperty(binding.name + ".shortcut2",binding.shortcut2);
		}
	}

	class KeyCompare implements MiscUtilities.Compare
	{
		int col;

		KeyCompare(int col)
		{
			this.col = col;
		}

		public int compare(Object obj1, Object obj2)
		{
			ShortcutsOptionPane.KeyBinding k1 = (ShortcutsOptionPane.KeyBinding)obj1;
			ShortcutsOptionPane.KeyBinding k2 = (ShortcutsOptionPane.KeyBinding)obj2;

			String label1 = k1.label.toLowerCase();
			String label2 = k2.label.toLowerCase();

			if(col == 0)
				return label1.compareTo(label2);
			else
			{
				String shortcut1, shortcut2;

				if(col == 1)
				{
					shortcut1 = k1.shortcut1;
					shortcut2 = k2.shortcut1;
				}
				else
				{
					shortcut1 = k1.shortcut2;
					shortcut2 = k2.shortcut2;
				}

				if(shortcut1 == null && shortcut2 != null)
					return 1;
				else if(shortcut2 == null && shortcut1 != null)
					return -1;
				else if(shortcut1 == null && shortcut2 == null)
					return label1.compareTo(label2);
				else
					return shortcut1.compareTo(shortcut2);
			}
		}
	}
}
