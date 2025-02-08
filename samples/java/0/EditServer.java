/*
 * EditServer.java - jEdit server
 * Copyright (C) 1999, 2000 Slava Pestov
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

package org.gjt.sp.jedit;

import javax.swing.SwingUtilities;
import java.io.*;
import java.net.*;
import java.util.Random;
import java.util.Vector;
import org.gjt.sp.util.Log;

/**
 * @author Slava Pestov
 * @version $Id: EditServer.java,v 1.23 2001/04/22 04:32:31 sp Exp $
 */
class EditServer extends Thread
{
	EditServer(String portFile)
	{
		super("jEdit server daemon [" + portFile + "]");
		setDaemon(true);
		this.portFile = portFile;

		try
		{
			socket = new ServerSocket(0); // Bind to any port
			authKey = Math.abs(new Random().nextInt());
			int port = socket.getLocalPort();

			FileWriter out = new FileWriter(portFile);
			out.write(String.valueOf(port));
			out.write("\n");
			out.write(String.valueOf(authKey));
			out.write("\n");
			out.close();

			Log.log(Log.DEBUG,this,"jEdit server started on port "
				+ socket.getLocalPort());
			Log.log(Log.DEBUG,this,"Authorization key is "
				+ authKey);

			ok = true;
		}
		catch(IOException io)
		{
			/* on some Windows versions, connections to localhost
			 * fail if the network is not running. To avoid
			 * confusing newbies with weird error messages, log
			 * errors that occur while starting the server
			 * as NOTICE, not ERROR */
			Log.log(Log.NOTICE,this,io);
		}
	}

	public boolean isOK()
	{
		return ok;
	}

	public void run()
	{
		try
		{
			for(;;)
			{
				Socket client = socket.accept();
				Log.log(Log.MESSAGE,this,client + ": connected");

				BufferedReader in = new BufferedReader(
					new InputStreamReader(client.getInputStream()));

				try
				{
					int key = Integer.parseInt(in.readLine());
					if(key != authKey)
					{
						Log.log(Log.ERROR,this,
							client + ": wrong"
							+ " authorization key");
						in.close();
						client.close();
						return;
					}
				}
				catch(Exception e)
				{
					Log.log(Log.ERROR,this,
							client + ": invalid"
							+ " authorization key");
					in.close();
					client.close();
					return;
				}

				Log.log(Log.DEBUG,this,client + ": authenticated"
					+ " successfully");
				handleClient(client,in);

				client.close();
			}
		}
		catch(IOException io)
		{
			Log.log(Log.ERROR,this,io);
		}
	}

	void stopServer()
	{
		stop();
		new File(portFile).delete();
	}

	// private members
	private String portFile;
	private ServerSocket socket;
	private int authKey;
	private boolean ok;

	// Thread-safe wrapper for jEdit.newView()
	private void TSnewView(final Buffer buffer)
	{
		SwingUtilities.invokeLater(new Runnable() {
			public void run()
			{
				View view = jEdit.newView(jEdit.getFirstView(),
					buffer);
				view.requestFocus();
				view.toFront();
			}
		});
	}

	// Thread-safe wrapper for jEdit.newFile()
	private Buffer TSnewFile()
	{
		final Buffer[] retVal = new Buffer[1];
		try
		{
			SwingUtilities.invokeAndWait(new Runnable() {
				public void run()
				{
					retVal[0] = jEdit.newFile(null);
				}
			});
		}
		catch(Exception e)
		{
			Log.log(Log.ERROR,this,e);
		}
		return retVal[0];
	}

	// Thread-safe wrapper for jEdit.openFile()
	private Buffer TSopenFiles(final String parent, final String[] args)
	{
		final Buffer[] retVal = new Buffer[1];
		try
		{
			SwingUtilities.invokeAndWait(new Runnable() {
				public void run()
				{
					retVal[0] = jEdit.openFiles(parent,args);
				}
			});
		}
		catch(Exception e)
		{
			Log.log(Log.ERROR,this,e);
		}
		return retVal[0];
	}

	// Thread-safe wrapper for Sessions.loadSession()
	private Buffer TSrestoreOpenFiles()
	{
		final Buffer[] retVal = new Buffer[0];
		try
		{
			SwingUtilities.invokeAndWait(new Runnable() {
				public void run()
				{
					retVal[0] = jEdit.restoreOpenFiles();
				}
			});
		}
		catch(Exception e)
		{
			Log.log(Log.ERROR,this,e);
		}
		return retVal[0];
	}

	// Thread-safe wrapper for View.setBuffer()
	private void TSsetBuffer(final View view, final Buffer buffer)
	{
		SwingUtilities.invokeLater(new Runnable() {
			public void run()
			{
				view.setBuffer(buffer);
			}
		});
	}

	private void handleClient(Socket client, BufferedReader in)
		throws IOException
	{
		boolean readOnly = false;
		boolean newView = false;
		String parent = null;
		boolean restore = jEdit.getBooleanProperty("restore");
		boolean endOpts = false;

		View view = null;
		Vector args = new Vector();

		String command;
		while((command = in.readLine()) != null)
		{
			if(endOpts)
				args.addElement(command);
			else
			{
				if(command.equals("--"))
					endOpts = true;
				else if(command.equals("readonly"))
					readOnly = true;
				else if(command.equals("newview"))
					newView = true;
				else if(command.startsWith("parent="))
					parent = command.substring(7);
				else if(command.startsWith("norestore"))
					restore = false;
				else
				{
					Log.log(Log.ERROR,this,client
						+ ": unknown server"
						+ " command: " + command);
					in.close();
					socket.close();
					stopServer();
				}
			}
		}

		String[] _args = new String[args.size()];
		args.copyInto(_args);
		Buffer buffer = TSopenFiles(parent,_args);

		if(buffer == null && restore)
			buffer = TSrestoreOpenFiles();

		if(buffer == null)
			buffer = TSnewFile();

		// Create new view
		if(!newView)
			view = jEdit.getFirstView();

		if(view != null)
		{
			TSsetBuffer(view,buffer);
			view.requestFocus();
			view.toFront();
		}
		else
			TSnewView(buffer);
	}
}
