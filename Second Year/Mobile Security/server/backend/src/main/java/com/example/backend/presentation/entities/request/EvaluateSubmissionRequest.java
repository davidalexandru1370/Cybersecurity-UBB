package com.example.backend.presentation.entities.request;

public class EvaluateSubmissionRequest {
    private Float grade;
    private String feedback;

    public EvaluateSubmissionRequest() {
    }

    public EvaluateSubmissionRequest(Float grade, String feedback) {
        this.grade = grade;
        this.feedback = feedback;
    }

    public Float getGrade() {
        return grade;
    }

    public String getFeedback() {
        return feedback;
    }
}
