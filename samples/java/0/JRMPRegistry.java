/**
 * Copyright (C) 2002,2005 - INRIA (www.inria.fr)
 *
 * CAROL: Common Architecture for RMI ObjectWeb Layer
 *
 * This library is developed inside the ObjectWeb Consortium,
 * http://www.objectweb.org
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307
 * USA
 *
 * --------------------------------------------------------------------------
 * $Id: JRMPRegistry.java 398 2005-03-03 16:11:03Z benoitf $
 * --------------------------------------------------------------------------
 */
package org.objectweb.carol.jndi.ns;

import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import java.rmi.server.UnicastRemoteObject;
import java.util.Properties;

import org.objectweb.carol.jndi.registry.ManageableRegistry;
import org.objectweb.carol.rmi.util.PortNumber;
import org.objectweb.carol.util.configuration.CarolDefaultValues;
import org.objectweb.carol.util.configuration.TraceCarol;

/**
 * Class <code> JRMPRegistry </code>
 * @author Guillaume Riviere (Guillaume.Riviere@inrialpes.fr)
 * @version 1.0, 15/01/2003
 */
public class JRMPRegistry implements NameService {

    /**
     * Hostname to use
     */
    private String host = null;

    /**
     * port number (1099 for default)
     */
    public static int port = 1099;

    /**
     * Instance port number (firewall)
     */
    private static int objectPort = 0;

    /**
     * Configuration properties (of carol.properties)
     */
    private Properties configurationProperties = null;

    /**
     * registry
     */
    public static Registry registry = null;

    /**
     * start Method, Start a new NameService or do nothing if the name service
     * is all ready start
     * @param int port is port number
     * @throws NameServiceException if a problem occure
     */
    public void start() throws NameServiceException {
        if (TraceCarol.isDebugJndiCarol()) {
            TraceCarol.debugJndiCarol("JRMPRegistry.start() on port:" + port);
        }
        try {
            if (!isStarted()) {

                // Fix jrmp port if running inside a server
                if (System.getProperty(CarolDefaultValues.SERVER_MODE, "false").equalsIgnoreCase("true")) {
                    if (configurationProperties != null) {
                        String propertyName = CarolDefaultValues.SERVER_JRMP_PORT;
                        int jrmpPort = PortNumber.strToint(configurationProperties.getProperty(propertyName, "0"), propertyName);
                        if (jrmpPort > 0) {
                            TraceCarol.infoCarol("Using JRMP fixed server port number '" + jrmpPort + "'.");
                            objectPort = jrmpPort;
                        }
                    } else {
                        TraceCarol.debugCarol("No properties '" + CarolDefaultValues.SERVER_IIOP_PORT + "' defined in carol.properties file.");
                    }
                }


                if (port >= 0) {
                    registry = ManageableRegistry.createManagableRegistry(port, objectPort);
                    // add a shudown hook for this process
                    Runtime.getRuntime().addShutdownHook(new Thread() {

                        public void run() {
                            try {
                                JRMPRegistry.this.stop();
                            } catch (Exception e) {
                                TraceCarol.error("JRMPRegistry ShutdownHook problem", e);
                            }
                        }
                    });
                } else {
                    if (TraceCarol.isDebugJndiCarol()) {
                        TraceCarol.debugJndiCarol("Can't start JRMPRegistry, port=" + port + " is < 0");
                    }
                }
            } else {
                if (TraceCarol.isDebugJndiCarol()) {
                    TraceCarol.debugJndiCarol("JRMPRegistry is already start on port:" + port);
                }
            }
        } catch (Exception e) {
            throw new NameServiceException("can not start rmi registry: " + e);
        }
    }

    /**
     * stop Method, Stop a NameService or do nothing if the name service is all
     * ready stop
     * @throws NameServiceException if a problem occure
     */
    public void stop() throws NameServiceException {
        if (TraceCarol.isDebugJndiCarol()) {
            TraceCarol.debugJndiCarol("JRMPRegistry.stop()");
        }
        try {
            if (registry != null) UnicastRemoteObject.unexportObject(registry, true);
            registry = null;
        } catch (Exception e) {
            throw new NameServiceException("can not stop rmi registry: " + e);
        }
    }

    /**
     * isStarted Method, check if a name service is local
     * @return boolean true if the name service is local
     */
    public static boolean isLocal() {
        if (registry != null) {
            return true;
        } else {
            return false;
        }
    }

    /**
     * isStarted Method, check if a name service is started
     * @return boolean true if the name service is started
     */
    public boolean isStarted() {
        if (registry != null) return true;
        try {
            //TODO: Warning LocateRegistry Problem we are not in case of local
            // computer registry ....
            LocateRegistry.getRegistry(port).list();
        } catch (RemoteException re) {
            return false;
        }
        return true;
    }

    /**
     * set port method, set the port for the name service
     * @param int port number
     */
    public void setPort(int p) {
        if (TraceCarol.isDebugJndiCarol()) {
            TraceCarol.debugJndiCarol("JRMPRegistry.setPort(" + p + ")");
        }
        if (p != 0) {
            port = p;
        }
    }

    /*
     * (non-Javadoc)
     * @see org.objectweb.carol.jndi.ns.NameService#getPort()
     */
    public int getPort() {
        return port;
    }

    /**
     * Set the address to use for bind
     * @param host hostname/ip address
     */
    public void setHost(String host) {
        this.host = host;
    }

    /**
     * @return hostname/ip to use
     */
     public String getHost() {
         return host;
     }

     /**
      * Set the configuration properties of the protocol
      * @param p configuration properties
      */
     public void setConfigProperties(Properties p) {
         this.configurationProperties = p;
     }
}