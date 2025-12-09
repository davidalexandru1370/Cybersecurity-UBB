package com.example.backend.presentation.entities.request;

public class SubmitAssignmentRequest {
    private String content;

    public SubmitAssignmentRequest() {
    }

    public SubmitAssignmentRequest(String content) {
        this.content = content;
    }

    public String getContent() {
        return content;
    }
}
