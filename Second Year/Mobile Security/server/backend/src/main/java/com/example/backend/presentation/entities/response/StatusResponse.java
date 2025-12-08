package com.example.backend.presentation.entities.response;

import java.util.Date;

public class StatusResponse {
    private String status;
    private Date timestamp;
    private String version;

    public StatusResponse(String status, Date timestamp, String version) {
        this.status = status;
        this.timestamp = timestamp;
        this.version = version;
    }

    public String getStatus() {
        return status;
    }

    public Date getTimestamp() {
        return timestamp;
    }

    public String getVersion() {
        return version;
    }
}
