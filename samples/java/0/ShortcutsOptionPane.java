/*
 * ShortcutsOptionPane.java - Shortcuts options panel
 * Copyright (C) 1999 Slava Pestov
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
import org.gjt.sp.jedit.*;

/**
 * Generic key binding editor.
 * @author Slava Pestov
 * @version $Id: ShortcutsOptionPane.java,v 1.6 2000/11/11 02:59:31 sp Exp $
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
		add(BorderLayout.CENTER,createKeyTableScroller());

		JPanel panel = new JPanel();
		label = new JButton(jEdit.getProperty("options.keys.sort.label"));
		label.addActionListener(new ActionHandler());
		panel.add(label);
		shortcut = new JButton(jEdit.getProperty("options.keys.sort.shortcut"));
		shortcut.addActionListener(new ActionHandler());
		panel.add(shortcut);
		add(BorderLayout.SOUTH,panel);
	}

	protected void _save()
	{
		if(keyTable.getCellEditor() != null)
			keyTable.getCellEditor().stopCellEditing();

		keyModel.save();
	}

	// private members
	private JTable keyTable;
	private JButton label;
	private JButton shortcut;
	private ShortcutsModel keyModel;

	private JScrollPane createKeyTableScroller()
	{
		keyModel = createShortcutsModel();
		keyTable = new JTable(keyModel);
		keyTable.getTableHeader().setReorderingAllowed(false);
		Dimension d = keyTable.getPreferredSize();
		d.height = Math.min(d.height,200);
		JScrollPane scroller = new JScrollPane(keyTable);
		scroller.setPreferredSize(d);
		return scroller;
	}

	private ShortcutsModel createShortcutsModel()
	{
		return new ShortcutsModel(createBindings());
	}

	public static class KeyBinding
	{
		KeyBinding(String name, String label, String shortcut)
		{
			this.name = name;
			this.label = label;
			this.shortcut = shortcut;
		}

		String name;
		String label;
		String shortcut;
	}

	class ActionHandler implements ActionListener
	{
		public void actionPerformed(ActionEvent evt)
		{
			keyModel.sort(evt.getSource() == label ? 0 : 1);
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
		return 2;
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
			return binding.shortcut;
		default:
			return null;
		}
	}

	public boolean isCellEditable(int row, int col)
	{
		return (col == 1);
	}

	public void setValueAt(Object value, int row, int col)
	{
		if(col != 1)
			return;
		((ShortcutsOptionPane.KeyBinding)bindings.elementAt(row))
			.shortcut = (String)value;
		fireTableRowsUpdated(row,row);
	}

	public String getColumnName(int index)
	{
		switch(index)
		{
		case 0:
			return jEdit.getProperty("options.keys.name");
		case 1:
			return jEdit.getProperty("options.keys.binding");
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
			jEdit.setProperty(binding.name + ".shortcut",binding.shortcut);
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
				String shortcut1 = k1.shortcut;
				String shortcut2 = k2.shortcut;

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

/*
 * ChangeLog:
 * $Log: ShortcutsOptionPane.java,v $
 * Revision 1.6  2000/11/11 02:59:31  sp
 * FTP support moved out of the core into a plugin
 *
 * Revision 1.5  2000/04/28 09:29:12  sp
 * Key binding handling improved, VFS updates, some other stuff
 *
 * Revision 1.4  2000/04/18 11:44:31  sp
 * Context menu editor finished
 *
 * Revision 1.3  2000/04/16 08:56:24  sp
 * Option pane updates
 *
 * Revision 1.2  2000/02/15 07:44:30  sp
 * bug fixes, doc updates, etc
 *
 * Revision 1.1  1999/12/19 08:12:34  sp
 * 2.3 started. Key binding changes  don't require restart, expand-abbrev renamed to complete-word, new splash screen
 *
 */
